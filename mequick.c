/*-------------------------------------------------------------------------*/
/* Copyright 2013-2020 Armin Biere Johannes Kepler University Linz Austria */
/*-------------------------------------------------------------------------*/

#include "lglib.h"
#include "lgldimacs.h"

/*------------------------------------------------------------------------*/

#include <assert.h>
#include <ctype.h>
#include <limits.h>
#include <signal.h>
#include <stdarg.h>
#include <string.h>
#include <sys/time.h>
#include <unistd.h>

/*------------------------------------------------------------------------*/

#define MINCLIM 	100	// minimum conflict limit
#define MAXCLIM 	10000	// maximum conflict limit
#define SIMPINT 	1000	// simplification interval
#define REDINT  	1000	// reduce interval
#define MULTINIT	100	// initial multi runs
#define MULTINT 	4	// multi refinement interval
#define BBINT		10	// back-bone search interval
#define RANDF		5	// forced random factor
#define OPTDEF		3	// number of preprocessing rounds

/*------------------------------------------------------------------------*/

#define NEW(PTR,NUM) \
do { \
  size_t BYTES = (NUM) * sizeof *(PTR); \
  (PTR) = malloc (BYTES); \
  if (!(PTR)) { err ("out of memory"); exit (1); } \
  memset ((PTR), 0, BYTES); \
  incmem (BYTES); \
} while (0)

#define DEL(PTR,NUM) \
do { \
  size_t BYTES = (NUM) * sizeof *(PTR); \
  decmem (BYTES); \
  free (PTR); \
} while (0)

#define PUSH(STACK,ELEM) \
do { \
  if (size ## STACK == num ## STACK) { \
    size_t NEW_SIZE = size ## STACK; \
    size_t OLD_BYTES = NEW_SIZE * sizeof *STACK, NEW_BYTES; \
    if (NEW_SIZE) NEW_SIZE *= 2; else NEW_SIZE = 1; \
    NEW_BYTES = NEW_SIZE * sizeof *STACK; \
    decmem (OLD_BYTES); \
    STACK = realloc (STACK, NEW_BYTES); \
    if (!STACK) { err ("out of memory"); exit (1); } \
    incmem (NEW_BYTES); \
    size ## STACK = NEW_SIZE; \
  } \
  STACK[num ## STACK ++] = (ELEM); \
} while (0)

#define POP(STACK) \
 (assert (num ## STACK > 0), STACK[--num ## STACK])

/*------------------------------------------------------------------------*/

#define BPP	512				// bits per point
#define WPP	(BPP/sizeof(Word)/8)		// words per point
#define UPW	(sizeof(Word)/sizeof(unsigned))	// 'unsigned' per word

#if __GNUC__ && __GCC__ >= 4 && __GCC_MAJOR__ >= 6
typedef unsigned __int128 Word;			// GCC specific! (faster?)
#else
typedef unsigned long long Word;		// more portable ...
#endif

#define NEG_POINT(P) \
do { \
  int I; \
  for (I = 0; I < (int) WPP; I++) \
    (P).word[I] = ~(P).word[I]; \
} while(0)

#define OR_POINT(P,Q) \
do { \
  int I; \
  for (I = 0; I < (int) WPP; I++) \
    (P).word[I] |= (Q).word[I]; \
} while(0)

#define XOR_POINT(P,Q) \
do { \
  int I; \
  for (I = 0; I < (int) WPP; I++) \
    (P).word[I] ^= (Q).word[I]; \
} while(0)

/*------------------------------------------------------------------------*/

typedef enum Status Status;
typedef struct Point Point;

/*------------------------------------------------------------------------*/

enum Status { ACTIVE = 0, SINGLETON = 1, EQUIVALENT = 2, FIXED = 3, };

struct Point { Word word[WPP]; };

/*------------------------------------------------------------------------*/

static size_t currentbytes, maxbytes;

/*------------------------------------------------------------------------*/

static int minclim = MINCLIM;
static int maxclim = MAXCLIM;

/*------------------------------------------------------------------------*/

static int * cands, sizecands, numcands;
static int * bbcands, sizebbcands, numbbcands;
static int maxvar, speclauses, simpclauses;
static int ** clauses, sizeclauses, numclauses;
static int inconsistent, initialized, clim, useorder;
static int nextcandrandom, limhitreported, bceremain;
static int * parts, sizeparts, numparts, necs, oldnecs, oldactive;
static signed char * inactive, * cared;
static int numinactive, numcared;
static unsigned char * vals;
static int * care, sizecare, numcare, carevars, careclauses;
static int * part, * repr, * order, * stable, numstable;
static int * clause, sizeclause, numclause;
static LGL * globalgl, * bcelgl;
static const char * carepath;
static int * rcs, sizercs;
static Point * points;
static FILE * msgfile;

/*------------------------------------------------------------------------*/

static struct {
  struct { int rand, nonrand; } cands;
  struct { int total, single, multi; } splits;
  int reprs, fixed, melted, nonreusable;
  int merged, singletons, dropped, filled;
  struct { double time; int count; }
    bce, prep, order, refine, multi, merge, cand, implies,
    backbone, simp, reduce,
    solver, sat, unsat, unknown,
    bpmodel, smodel;
} stats;

static struct { struct { unsigned u, v; } rds; unsigned lim; } drop;

static struct { unsigned z, w; } rng;

struct { int multi, simp, reduce, bb; } limits;

/*------------------------------------------------------------------------*/

static int verbose, noutput, nosimp, norepr, nofixed, reverse, noblocked;
static int timelim, norandphase, norandcand, noreduce, norder, forceorder;
static int nomulti, nodrop = 1, optimize = OPTDEF, append, nostable = 1;

/*------------------------------------------------------------------------*/

static volatile sig_atomic_t timesup, catchedsig;
static struct itimerval oldtimer;

static void (*sig_int_handler)(int);
static void (*sig_segv_handler)(int);
static void (*sig_abrt_handler)(int);
static void (*sig_term_handler)(int);
static void (*sig_alrm_handler)(int);

/*------------------------------------------------------------------------*/

static void err (const char * fmt, ...) {
  va_list ap;
  fputs ("*** mequick: ", stderr);
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  fflush (stderr);
  exit (1);
}

static void msg (int level, const char * fmt, ...) {
  va_list ap;
  if (verbose < level) return;
  fputs ("c [mequick] ", stdout);
  va_start (ap, fmt);
  vfprintf (stdout, fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

/*------------------------------------------------------------------------*/

void mysrand (unsigned long long seed) {
  unsigned z = seed >> 32, w = seed;
  if (!z) z = ~z;
  if (!w) w = ~w;
  rng.z = z, rng.w = w;
}

static unsigned myrand () {
  unsigned res;
  rng.z = 36969 * (rng.z & 65535) + (rng.z >> 16);
  rng.w = 18000 * (rng.w & 65535) + (rng.w >> 16);
  res = (rng.z << 16) + rng.w;
  return res;
}

static unsigned myrandmod (unsigned mod) {
  unsigned res = myrand ();
  assert (mod >= 1);
  res %= mod;
  return res;
}

static unsigned myrandbit () { 
  unsigned bit = myrandmod (2);
  assert (bit == 0 || bit == 1);
  return bit;
}

/*------------------------------------------------------------------------*/

static double avg (double a, double b) { return b ? a / b : 0; }
static double pcnt (double a, double b) { return avg (100*a, b); }

/*------------------------------------------------------------------------*/

static void incmem (size_t bytes) {
  currentbytes += bytes;
  if (currentbytes > maxbytes) maxbytes = currentbytes;
}

static void decmem (size_t bytes) {
  assert (currentbytes >= bytes);
  currentbytes -= bytes;
}

static void * alloc (void * dummy, size_t bytes) {
  char * res;
  NEW (res, bytes);
  (void) dummy;
  return res;
}

static void dealloc (void * dummy, void * void_ptr, size_t bytes) {
  char * char_ptr = void_ptr;
  DEL (char_ptr, bytes);
  (void) dummy;
}

static void * resize (void * dummy, void * ptr, 
                      size_t old_bytes, size_t new_bytes) {
  assert (currentbytes >= old_bytes);
  currentbytes -= old_bytes;
  currentbytes += new_bytes;
  if (currentbytes > maxbytes) maxbytes = currentbytes;
  (void) dummy;
  return realloc (ptr, new_bytes);
}

/*------------------------------------------------------------------------*/

static void deactivate (int lit) {
  int idx = abs (lit);
  if (inactive[idx]) return;
  inactive[idx] = 1;
  numinactive++;
  if (stable[idx]) {
    assert (numstable > 0);
    numstable--;
    stable[idx] = 0;
  }
}

static void melt (int lit) {
  assert (lit);
  assert (lglfrozen (globalgl, lit) == 1);
  lglmelt (globalgl, lit);
  stats.melted++;
  deactivate (lit);
}

/*------------------------------------------------------------------------*/

static int chase (int a) {
  int res, next = a, tmp;
  do {
    res = next;
    assert (res);
    assert (abs (res) <= maxvar);
    next = repr[abs (res)];
    if (res < 0) next = -next;
    assert (next != -res);
  } while (next != res);
  for (tmp = a; tmp != res; tmp = next) {
    int n, o;
    assert (tmp);
    assert (abs (tmp) <= maxvar);
    next = repr[abs (tmp)];
    if (tmp < 0) next = -next;
    assert (next != -res);
    o = repr[abs (tmp)];
    n = (tmp < 0) ? -res : res;
    repr[abs (tmp)] = n;
    if (o != n) deactivate (tmp);
  }
  assert (repr[abs (a)] == ((a < 0) ? -res : res));
  assert (repr[abs (res)] == abs (res));
  return res;
}

static void mergeaux (int a, int b) {
  int r = chase (a), s = chase (b);
  assert (r != -s);
  if (r == s) return;
#ifndef NDEBUG
  if (!inactive[abs (a)] && !inactive[abs (b)]) {
    assert (part[abs (a)] == part [abs (b)]);
    assert (part[abs (a)] == part [abs (r)]);
    assert (part[abs (b)] == part [abs (s)]);
  }
#endif
  if (abs (r) > abs (s)) { int tmp = r; r = s, s = tmp; }
  assert (abs (r) < abs (s));
  if (s < 0) { s = -s, r = -r; }
  assert (s > 0);
  repr[s] = r;
  deactivate (s);
}

static void mergerepr () {
  int lit;
  if (norepr) return;
  for (lit = 1; lit <= maxvar; lit++) {
    int r = chase (lit);
    int o = chase (lglrepr (globalgl, r));
    assert (o != -r);
    if (o == r) continue;
    msg (3, "merge repr %d %d", o, r);
    mergeaux (o, r);
    stats.reprs++;
  }
}

static void check () {
#if 0
  {
    int i, s = 0;
    for (i = 0; i < numparts; i++) {
      int lit = parts[i];
      if (s == i) printf ("[%d] ", s); 
      if (lit) printf ("%d ", lit);
      else printf ("0\n"), s = i + 1;
    }
  }
#endif
#ifdef NDEBUG
  int start, end;
  for (start = 0; start < numparts; start = end + 1) {
    int lit;
    for (end = start; (lit = parts[end]); end++) {
      assert (part [abs (lit)] == start);
      assert (repr [abs (lit)] == abs (lit));
    }
    assert (end - start > 1);
  }
#endif
}

static void report () {
  int eq = stats.merged + stats.reprs;
  int active = maxvar - numinactive;
  if (verbose < 2 && active == oldactive && oldnecs == necs) return;
  assert (numinactive >= 0);
  assert (active >= 0);
  msg (1,
    "%.1f sec, "
    "%d act %.0f%%, "
    "%d fxd %.0f%%, "
    "%d eqs %.0f%% (%d mrg %.0f%%, %d rpr %.0f%%), "
    "%d sgt %.0f%%, "
    "%d lim, "
    "%d cls, "
    "%d spt, "
    "%d ecs, "
    "%d stb",
    lglprocesstime (),
    active, pcnt (active, maxvar),
    stats.fixed, pcnt (stats.fixed, maxvar),
    eq, pcnt (eq, maxvar),
    stats.merged, pcnt (stats.merged, eq),
    stats.reprs, pcnt (stats.reprs, eq),
    stats.singletons, pcnt (stats.singletons, maxvar),
    clim,
    stats.solver.count,
    stats.splits.total,
    necs,
    numstable);
  oldactive = active, oldnecs = necs;
}

/*------------------------------------------------------------------------*/

static void flush () {
  int i, j = 0, lit, start, removed, deltafixed, deltasons;
  mergerepr ();
  j = start = removed = deltafixed = deltasons = 0;
  for (i = 0; i < numparts; i++) {
    lit = parts[i];
    if (lit) {
      if (!nofixed && lglfixed (globalgl, lit)) {
	deactivate (lit);
	deltafixed++;
	stats.fixed++;
      } else if (chase (lit) == lit) {
	parts[j++] = lit;
	part[abs (lit)] = start;
      } else removed++, deactivate (lit);
    } else if (start != j) {
      assert (start < j);
      if (start + 1 == j) { 
	melt (parts[start]);
	deltasons++;
	stats.singletons++;
	j--;
      } else parts[j++] = 0, start = j;
      assert (start == j);
    }
  }
  numparts = j;
  necs = 0;
  for (i = 0; i < numparts; i++)
    if (!parts[i]) necs++;
  msg (2,
    "removed %d fixed, %d equivalent and %d singleton literals from partition",
    deltafixed, removed, deltasons);

  check ();
  report ();

  if (!nodrop && !nextcandrandom) {
    if (!--drop.lim) {
      if (drop.rds.v + numinactive > (unsigned) maxvar) drop.rds.u = drop.rds.v = 1;
      else if ((drop.rds.u & -drop.rds.u) != drop.rds.v) drop.rds.v *= 2;
      else drop.rds.u++, drop.rds.v = 1;
      msg (2, "dropping and setting new drop limit %d", drop.rds.v);
      drop.lim = drop.rds.v;
      stats.dropped++;
      numcands = 0;
    } else msg (2, "flushing but no dropping (%d remain)", drop.lim);
  }
}

/*------------------------------------------------------------------------*/

static void singlemodel () {
  double start, delta;
  int i, randval = 0;
  const int * p;
  start = lglprocesstime ();
  msg (2, "starting single model construction");
  assert (!noblocked);
  assert (!bceremain);
  for (i = 1; i <= maxvar; i++) {
    int ival = lglfixed (globalgl, i), repr;
    unsigned char val;
    if (ival < 0) val = 0;
    else if (ival > 0) val = 1;
    else if ((repr = chase (i)) != i) {
      val = vals [abs (repr)];
      if (repr < 0) val = !val;
    } else randval++, val = myrandbit ();
    vals[i] = val;
  }
  msg (2,
    "initialized %d variable, %d randomly %.0f%%",
    maxvar, randval, pcnt (randval, maxvar));
  p = rcs + sizercs;
  if (p > rcs) p--;
  while (p > rcs) {
    unsigned sum = 0, val;
    int last = 0, lit;
    assert (!*p);
    while (p > rcs && (lit = *--p)) {
      val = vals[abs (lit)];
      if (lit < 0) val = !val;
      sum |= val;
      last = lit;
    }
    assert (last);
    lit = abs (last);
    val = vals[lit];
    val ^= !sum;
    vals[lit] = val;
  }
  delta = lglprocesstime () - start;
  msg (2,
    "finished single model construction in %.2f seconds",
    delta);
  stats.smodel.time += delta;
  stats.smodel.count++;
}

static void bitparallelmodel () {
  int i, j, k, randval = 0;
  double start, delta;
  const int * p;
  start = lglprocesstime ();
  msg (2, "starting bit-parallel model construction");
  assert (!noblocked);
  assert (!bceremain);
  for (i = 1; i <= maxvar; i++) {
    int repr, ival = lglfixed (globalgl, i);
    Point p;
    if (ival < 0) memset (&p, 0, sizeof p);
    else if (ival > 0) memset (&p, 0xff, sizeof p);
    else if ((repr = chase (i)) != i) {
      assert (abs (repr) < i);
      p = points[abs (repr)];
      if (repr < 0) NEG_POINT (p);
    } else {
      for (j = 0; j < (int) WPP; j++) {
	Word w = 0;
	for (k = 0; k < (int) UPW; k++) {
	  w <<= 32;
	  w |= myrand ();
	  randval++;
	}
	p.word[j] = w;
      }
    }
    points[i] = p;
  }
  msg (2,
    "initialized %d points with %d random words %.0f%%",
    maxvar, randval, pcnt (randval, maxvar));
  p = rcs + sizercs;
  if (p > rcs) p--;
  while (p > rcs) {
    int last = 0, lit;
    Point sum, val;
    memset (&sum, 0, sizeof sum);
    assert (!*p);
    while (p > rcs && (lit = *--p)) {
      val = points[abs (lit)];
      if (lit < 0) NEG_POINT (val);
      OR_POINT (sum, val);
      last = lit;
    }
    assert (last);
    lit = abs (last);
    val = points[lit];
    NEG_POINT (sum);
    XOR_POINT (val, sum);
    points[lit] = val;
  }
  delta = lglprocesstime () - start;
  msg (2,
    "finished bit-parallel model construction in %.2f seconds",
    delta);
  stats.bpmodel.time += delta;
  stats.bpmodel.count++;
}

static int cmpartaux (int a, int b) {
  Point p = points [abs (a)], q = points [abs (b)];
  int i;
  for (i = 0; i < (int) WPP; i++) {
    Word u = p.word[i], v = q.word[i];
    if (a < 0) u = ~u;
    if (b < 0) v = ~v;
    if (u < v) return -1;
    if (u > v) return 1;
  }
  return 0;
}

static int cmpart (const void * p, const void * q) {
  return cmpartaux (* (int*) p, * (int*) q);
}

static int domulti () {
  if (nomulti) return 0;
  if (noblocked) return 0;
  if (bceremain) return 0;
  if (limits.reduce > stats.solver.count) return 0;
  limits.multi = stats.solver.count + MULTINT;
  return 1;
}

static void multirefine () {
  int * newparts, numnewparts, sizenewparts, start, end, i;
  double delta = lglprocesstime ();
  assert (!nomulti);
  assert (!noblocked);
  assert (!bceremain);
  stats.multi.count++;
  bitparallelmodel ();
  for (i = 1; i <= maxvar; i++) {
    int val, j;
    Point p;
    if (inactive[i]) continue;
    if (!(val = stable[i])) continue;
    p = points [i];
    if (val < 0) {
      for (j = 0; val && j < (int) WPP; j++)
	if (p.word[j]) val = 0;
    } else {
      assert (val > 0);
      for (j = 0; val && j < (int) WPP; j++)
	if (~p.word[j]) val = 0;
    }
    if (val) continue;
    assert (numstable > 0);
    stable[i] = 0;
    numstable--;
  }
  numnewparts = sizenewparts = 0;
  newparts = 0;
  for (start = 0; start < numparts; start = end + 1) {
    int prev, size, i;
    for (end = start; parts[end]; end++) assert (end + 1 < numparts);
    size = end - start;
    if (size > 1) qsort (parts + start, size, sizeof *parts, cmpart);
    prev = parts[start];
    PUSH (newparts, prev);
    for (i = start + 1; i < end; i++) {
      int lit = parts[i], cmp = cmpartaux (prev, lit);
      if (cmp < 0) {
	PUSH (newparts, 0);
	stats.splits.total++;
	stats.splits.multi++;
      }
      PUSH (newparts, lit);
      prev = lit;
    }
    PUSH (newparts, 0);
  }
  DEL (parts, sizeparts);
  parts = newparts, numparts = numnewparts, sizeparts = sizenewparts;
  flush ();
  delta = lglprocesstime () - delta;
  msg (2, "finished multiple refinement in %.2f seconds", delta);
  stats.multi.time += delta;
}

/*------------------------------------------------------------------------*/

static int limhit () {
  if (limhitreported) return 1;
  if (timelim && timesup) {
    msg (1, "time limit hit after %.2f seconds", lglprocesstime ());
    limhitreported = 1;
    return 1;
  }
  return 0;
}

/*------------------------------------------------------------------------*/

static int doreduce () {
  if (noreduce) return 0;
  if (limits.reduce > stats.solver.count) return 0;
  limits.reduce = stats.solver.count + REDINT;
  return 1;
}

static void reduce () {
  double start = lglprocesstime (), delta;
  stats.reduce.count++;
  msg (2,
    "reduction %d of learned clauses cache after %d SAT calls",
    stats.reduce.count, stats.solver.count);
  lglreducecache (globalgl);
  delta = lglprocesstime () - start;
  stats.reduce.time += delta;
}

/*------------------------------------------------------------------------*/

static int dosimp () {
  if (nosimp) return 0;
  if (limits.simp > stats.solver.count) return 0;
  limits.simp = stats.solver.count + SIMPINT;
  return 1;
}

static void simp () {
  double start = lglprocesstime ();
  stats.simp.count++;
  msg (2, "forced simplification %d after %d SAT calls", 
    stats.simp.count, stats.solver.count);
  (void) lglsimp (globalgl, 1);
  stats.simp.time += lglprocesstime () - start;
}

/*------------------------------------------------------------------------*/

static int sat () {
  double start = lglprocesstime (), delta;
  int res;
  msg (2, "SAT solver call %d", ++stats.solver.count);
  res = lglsat (globalgl);
  delta = lglprocesstime () - start;
  stats.solver.time += delta;
  if (res == 10) stats.sat.count++, stats.sat.time += delta;
  else if (res == 20) stats.unsat.count++, stats.unsat.time += delta;
  else stats.unknown.count++, stats.unknown.time += delta;
  msg (2, "SAT solver returns %d in call %d in %.02f seconds",
    res, stats.solver.count, delta);
  return res;
}

/*------------------------------------------------------------------------*/

static int term (void * dummy) {
  (void) dummy;
  return timelim && timesup;
}

static void setopts () {
  if (verbose) lglsetopt (globalgl, "verbose", verbose - 1);
  lglsetopt (globalgl, "bca", 0);
  lglseterm (globalgl, term, 0);
  lglsetout (globalgl, msgfile);
  lglsetprefix (globalgl, "c [mequick.globalgl] ");
}

/*------------------------------------------------------------------------*/

static void init () {
  double start, delta;
  int i;
  assert (!initialized);
  start = lglprocesstime ();
  drop.lim = drop.rds.u = drop.rds.v = 1;
  msgfile = stdout;
  NEW (repr, maxvar + 1);
  for (i = 1; i <= maxvar; i++) repr[i] = i;
  NEW (part, maxvar + 1);
  NEW (stable, maxvar + 1);
  NEW (order, maxvar + 1);
  NEW (points, maxvar + 1);
  NEW (inactive, maxvar + 1);
  NEW (cared, maxvar + 1);
  NEW (vals, maxvar + 1);
  globalgl = lglminit (0, alloc, resize, dealloc);
  setopts ();
  for (i = 0; i < numclauses; i++) {
    const int * c = clauses[i], * p;
    int lit;
    for (p = c; (lit = *p); p++)
      lgladd (globalgl, lit);
    lgladd (globalgl, 0);
  }
  if (!noblocked) bcelgl = lglclone (globalgl);
  delta = lglprocesstime () - start;
  msg (1,
    "initialized %s in %0.2f seconds",
    (norder ? "one SAT solver" : "two SAT solvers"),
    delta);
}

/*------------------------------------------------------------------------*/

static void initblocked () {
  double start, delta;
  int * p, * q, i;
  if (inconsistent) return;
  if (limhit ()) return;
  if (noblocked) {
    msg (1, "generation of reconstruction stack with BCE disabled");
    return;
  }
  start = lglprocesstime ();
  stats.bce.count++;
  msg (1, "generating reconstruction stack (disable with '--no-blocked')");
  assert (bcelgl);
  lglsetprefix (bcelgl, "c [mequick.bce] ");
  lglsetopt (bcelgl, "plain", 1);
  lglsetopt (bcelgl, "block", 1);
  lglsetopt (bcelgl, "blkrtc", 1);
  lglsetopt (bcelgl, "blkclslim", INT_MAX);
  lglsetopt (bcelgl, "blkocclim", INT_MAX);
  lglsetopt (bcelgl, "verbose", verbose-1);
  lglsetopt (bcelgl, "wait", 0);
  lglsetopt (bcelgl, "pure", 0);
  lglseterm (bcelgl, term, 0);
  lglmeltall (bcelgl);
  (void) lglsimp (bcelgl, 1);
  (void) limhit ();
  bceremain = lglnclauses (bcelgl);
  if (bceremain)
    msg (1, "%d clauses remain after BCE %.0f%%",
      bceremain, pcnt (bceremain, numclauses));
  else
    msg (1, "all clauses eliminated after BCE");
  lglreconstk (bcelgl, &p, &q);
  sizercs = q - p;
  NEW (rcs, sizercs);
  for (i = 0; i < sizercs; i++) rcs[i] = p[i];
  if (verbose > 1) lglstats (bcelgl);
  lglrelease (bcelgl);
  bcelgl = 0;
  delta = lglprocesstime () - start;
  msg (1,
    "extracted reconstruction stack of size %d (%.0f MB) in %.2f seconds",
    sizercs, (sizercs * sizeof *rcs)/(double)(1<<20), delta);
  stats.bce.time += delta;
}

/*------------------------------------------------------------------------*/

static void initorder () {
  int lit, prev, count, ordered, i;
  double start, delta;
  if (inconsistent) return;
  if (limhit ()) return;
  if (noblocked) {
    msg (1, "ordering of variables disabled (because of '--no-blocked')");
    return;
  }
  if (norder) {
    msg (1, "ordering of variables disabled (because of '--no-order')");
    return;
  }
  if (bceremain > 0 && !forceorder) {
    msg (1,
      "not using elimination order (%d clauses remain, use '--force-order')",
      bceremain);
    return;
  }
  start = lglprocesstime ();
  stats.order.count++;
  msg (1, "starting to order variables (disable with '--no-order')");
  for (lit = 1; lit <= maxvar; lit++) order[lit] = -1;
  prev = count = ordered = 0;
  for (i = 0; i < sizercs; i++) {
    lit = rcs[i];
    if (!prev) {
      int idx = abs (lit);
      if (order[idx] < 0) ordered++;
      order[idx] = count++;
    }
    prev = lit;
  }
  delta = lglprocesstime () - start;
  msg (1,
    "finished ordering %d variables %.0f%% in %.2f seconds",
    ordered, pcnt (ordered, maxvar), delta);
  stats.order.time += delta;
  useorder = 1;
}

/*------------------------------------------------------------------------*/

static void markcared (void * dummy, int lit) {
  int idx;
  (void) dummy;
  if (append) PUSH (care, lit);
  if (!lit) return;
  idx = abs (lit);
  if (idx > maxvar) return;
  assert (cared);
  if (cared[idx]) return;
  cared[idx] = 1;
  numcared++;
}

static void careheader (void * dummy, int v, int c) {
  (void) dummy;
  carevars = v, careclauses = c;
  msg (1, "parsed care file header 'p cnf %d %d'", v, c);
}

/*------------------------------------------------------------------------*/

static void preprocess () {
  int oldnclauses, newnclauses;
  int oldnvars, newnvars;
  double start, delta;
  LDR * ldr;
  int i;
  if (!carepath) {
    msg (1,
      "preprocessing disabled (no care file specified with '-c <path>')");
    return;
  }
  start = lglprocesstime ();
  stats.prep.count++;
  msg (1, "determining variables in care file '%s'", carepath);
  ldr = ldrminit (0, alloc, resize, dealloc);
  ldrsetpath (ldr, carepath);
  ldrsetadd (ldr, 0, markcared);
  ldrsetheader (ldr, 0, careheader);
  if (!ldrparse (ldr)) {
    fprintf (stderr, "%s\n", ldrerr (ldr));
    exit (1);
  }
  ldrelease (ldr);
  if (limhit ()) goto DONE;
  msg (1,
    "freezing %d common variables %.0f%% in care file",
    numcared, pcnt (numcared, maxvar));
  for (i = 1; i <= maxvar; i++)
    if (cared[i]) lglfreeze (globalgl, i);
  msg (1, "starting to run SAT preprocessing %d times", optimize);
  oldnvars = lglnvars (globalgl);
  assert (oldnvars <= maxvar);
  oldnclauses = lglnclauses (globalgl);
  lglsetprefix (globalgl, "c [mequick.preprocess] ");
  if (optimize > 0) {
    (void) lglsimp (globalgl, optimize);
    (void) limhit ();
  }
  newnvars = lglnvars (globalgl);
  newnclauses = lglnclauses (globalgl);
  msg (1, "reduced to %d variables %.0f%% and %d clauses %.0f%%",
    newnvars, pcnt (newnvars, oldnvars),
    newnclauses, pcnt (newnclauses, oldnclauses));
  for (i = 1; i <= maxvar; i++) {
    if (cared[i]) assert (!inactive[i]), lglmelt (globalgl, i);
    else if (lglreusable (globalgl, i))
      lglreuse (globalgl, i), assert (!inactive[i]);
    else deactivate (i), stats.nonreusable++;
  }
  if (verbose > 1) lglstats (globalgl);
DONE:
  delta = lglprocesstime () - start;
  msg (1,
    "%d non-usable variables %.0f%% after preprocessing in %.2f seconds",
    stats.nonreusable, pcnt (stats.nonreusable, maxvar), delta);
  msg (1,
    "%d active variables %.0f%% after preprocessing in %.2f seconds",
    maxvar - numinactive, pcnt (maxvar - numinactive,  maxvar), delta);
  stats.prep.time += delta;
}

/*------------------------------------------------------------------------*/

static void initpart () {
  int i, res, usepoints;
  double start;
  assert (!initialized);
  if (limhit ()) return;
  start = lglprocesstime ();
  msg (1,
     "starting to initialize partition at %.2f seconds",
    lglprocesstime ());

  for (i = 1; i <= maxvar; i++)
    if (!inactive [i])
      lglfreeze (globalgl, i);

  if (!noblocked && !bceremain) {
    msg (1, "reconstructing model to initialize partition");
    singlemodel ();
    usepoints = 1;
    res = 10;
  } else {
    msg (1, "using actual SAT solver call to initialize partition");
    lglsetprefix (globalgl, "c [mequick.init] ");
    res = sat ();
    (void) limhit ();
    if (verbose > 1) lglstats (globalgl);
    usepoints = 0;
  }

  if (res == 20) {
    assert (noblocked || bceremain > 0);
    assert (lglinconsistent (globalgl));
    msg (1, "formula is actually unsatisfiable");
    inconsistent = 1;
  } else if (res == 10) {
    int pos = 0, neg = 0;
    assert (!numparts);
    for (i = 1; i <= maxvar; i++) {
      int val;
      if (inactive[i]) continue;
      if (usepoints) val = vals[i] ? 1 : -1;
      else val = lglderef (globalgl, i);
      stable[i] = val, numstable++;
      if (val < 0) neg++; else pos++;
      assert (val == 1 || val == -1);
      PUSH (parts, val * i);
      part[i] = 0;
    }
    if (numparts) {
      PUSH (parts, 0);
      necs = 1;
    } else necs = 0;
    initialized = 1;
    msg (1,
      "first model has %d positive and %d negative values",
      pos, neg);
    flush ();
  } else {
    assert (timesup);
    msg (1, "failed to initialize partition due to time out");
  }
  msg (1,
    "initialization of partition took %.2f seconds",
    lglprocesstime () - start);
}

/*------------------------------------------------------------------------*/

static void header (void * dummy, int v, int c) {
  (void) dummy;
  maxvar = v;
  speclauses = c;
  msg (1, "found header 'p cnf %d %d'", v, c);
}

/*------------------------------------------------------------------------*/

static void add (void * dummy, int lit) {
  int * c;
  (void) dummy;
  PUSH (clause, lit); 
  if (lit) return;
  NEW (c, numclause);
  memcpy (c, clause, numclause * sizeof *c);
  numclause = 0;
  PUSH (clauses, c);
}

/*------------------------------------------------------------------------*/

static int cmpcands (const void * p, const void * q) {
  int oca, oda, ocb, odb, ocm, odm, res;
  int * c = (int *) p, * d = (int *) q;
  res = d[0] - c[0];
  if (res) return reverse ? -res : res;
  if (useorder) {
    oca = order[abs (c[1])], ocb = order[abs (c[2])];
    oda = order[abs (d[1])], odb = order[abs (d[2])];
    ocm = (oca < ocb) ? ocb : oca;
    odm = (oda < odb) ? odb : oda;
    res = ocm - odm;
    if (res) return res;
    assert (oca < 0 && ocb < 0 && oda < 0 && odb < 0);
  }
  res = d[1] - c[1];
  assert (res);
  return res;
}

static void fillcands () {
  int start, end, apos, bpos, a, b;
  msg (2, "filling candidates list");
  stats.filled++;
  assert (numparts > 0);
  for (start = 0; start < numparts; start = end + 1) {
    int size;
    for (end = start; parts[end]; end++)
      ;
    size = end - start;
    apos = size ? myrand () % size : 0;
    bpos = size ? myrand () % size : 0;
    if (bpos == apos && ++bpos == size) bpos = 0;
    assert (apos != bpos);
    a = parts[start + apos];
    b = parts[start + bpos];

    if (useorder) {
      int i;
      for (i = start; i < end; i++) {
	int lit = parts[i];
	if (order[abs (lit)] > order [abs (a)]) {
	  if (b == lit) b = a;
	  a = lit;
	}
      }
    }

    assert (a);
    assert (b);
    assert (abs (a) != abs (b));

    PUSH (cands, size);
    PUSH (cands, a);
    PUSH (cands, b);
  }
  assert (numcands > 0);
  assert (!(numcands % 3));
  msg (2, "sorting candidates list");
  qsort (cands, numcands/3, 3*sizeof*cands, cmpcands);
}

static int getcandpair (int * aptr, int * bptr) {
  int start, end, a, b, lit, size, apos, bpos;
  double delta;
  if (!numparts) return 0;
  delta = lglprocesstime ();
  stats.cand.count++;
  if (!norandcand &&
      (nextcandrandom || (maxvar - numinactive)/RANDF > necs)) {
    if (nextcandrandom) msg (2, "random candidate pair (per default)");
    else msg (2, "random candidate pair (not enough equivalence classes)");
    stats.cands.rand++;
    end = myrand () % numparts;
    for (start = end; start > 0 && parts[start-1]; start--)
      ;
    while (parts[end]) end++, assert (end < numparts);
    size = end - start;
    assert (size > 1);
    apos = myrand () % size;
    bpos = myrand () % size;
    if (apos == bpos) {
      if (++bpos == size) bpos = 0;
      assert (apos != bpos);
    }
    a = parts[start + apos], b = parts[start + bpos];
    nextcandrandom = 0;
  } else {
    msg (2, "non-random candidate pair from candidates list");
    stats.cands.nonrand++;
    for (;;) {
      int tmp;
      if (!numcands) fillcands ();
      b = POP (cands);
      a = POP (cands);
      tmp = POP (cands);
      if (inactive[abs (b)]) continue;
      if (inactive[abs (a)]) continue;
      start = part[abs (a)];
      if (start != part[abs (b)]) continue;
      for (end = start; (lit = parts[end]); end++) {
	if (lit == -a) a = -a;
	if (lit == -b) b = -b;
      }
      (void) tmp;
      size = end - start;
      assert (size <= tmp);
      assert (size > 1);
      break;
    }
    nextcandrandom = 1;
  }
  assert (abs (a) != abs (b));
  assert (part[abs (a)] == part[abs (b)]);
  if (!norandphase && myrandbit ()) { a = -a; b = -b; }
  delta = lglprocesstime () - delta;
  msg (2,
    "candidate pair %d %d in partition %d of size %d in %.2f seconds",
    a, b, part [abs (a)], size, delta);
  stats.cand.time += delta;
  *aptr = a, *bptr = b;
  return 1;
}

static void fillbbcands () {
  int i, k, val, lit;
  assert (!numbbcands);
  for (i = 1; i <= maxvar; i++) {
    if (inactive[i]) continue;
    if (!(val = stable[i])) continue;
    if (lglfixed (globalgl, i)) continue;
    lit = (val < 0) ? -i : i;
    PUSH (bbcands, lit);
    k = myrandmod (numbbcands);
    if (k < numbbcands) {
      bbcands[numbbcands-1] = bbcands[k];
      bbcands[k] = lit;
    }
  }
}

static int candbackbone (int * aptr) {
  int a;
  if (nostable) return 0;
  if (!numstable) return 0;
  if (limits.bb > stats.solver.count) return 0;
  limits.bb = stats.solver.count + BBINT;
  for (;;) {
    if (!numbbcands) fillbbcands ();
    if (!numbbcands) return 0;
    a = POP (bbcands);
    if (inactive[abs (a)]) continue;
    if (!stable[abs (a)]) continue;
    if (lglfixed (globalgl, a)) continue;
    break;
  }
  assert ((stable[abs (a)] < 0) == (a < 0));
  if (aptr) *aptr = a;
  msg (2, "back bone candidate %d", a);
  return 1;
}

static void inclim () {
  int oldclim = clim;
  clim += (minclim + 9) / 10;
  if (clim > maxclim) clim = maxclim;
  if (oldclim < clim) msg (2, "increment conflict limit to %d", clim);
  else msg (2, "could not increase conflict limit larger than %d", clim);
}

static void declim () {
  int oldclim = clim;
  assert (oldclim >= minclim);
  clim = clim/2;
  if (clim < minclim) clim = minclim;
  if (oldclim > clim) msg (2, "decremented conflict limit to %d", clim);
  else msg (2, "could not decrease conflict limit smaller than %d", clim);
}

static int implies (int a, int b) {
  double delta = lglprocesstime ();
  const char * restr;
  int res;
  stats.implies.count++;
  msg (2,
    "checking '%d -> %d' with conflict limit %d",
    a, b, clim);
  lglsetopt (globalgl, "clim", clim);

  lglassume (globalgl, a);
  lglassume (globalgl, -b);
  res = sat ();
  if (res == 10) restr = "failed";
  else if (res == 20) restr = "succeeded";
  else restr = "hits conflict limit";
  delta = lglprocesstime () - delta;
  msg (2, "implication check '%d -> %d' %s in %.2f seconds",
    a, b, restr, delta);
  stats.implies.time += delta;
  return res;
}

static void refine () {
  int * newparts, numnewparts, sizenewparts, i, start, end;
  double delta = lglprocesstime ();
  int lit, val, pos, neg;
  stats.refine.count++;
  numnewparts = sizenewparts = 0;
  newparts = 0;
  for (start = 0; start < numparts; start = end + 1) {

    for (end = start; parts[end]; end++)
      assert (end + 1 < numparts);
    assert (start + 1 < end);

    for (i = start; i < end; i++) {
      lit = abs (parts[i]);
      if (!stable[lit]) continue;
      val = lglderef (globalgl, lit);
      if (val == stable[lit]) continue;
      assert (numstable > 0);
      stable[lit] = 0;
      numstable--;
    }

    pos = 0;
    for (i = start; i < end; i++) {
      lit = parts[i];
      val = lglderef (globalgl, lit);
      if (val >= 0) continue;
      PUSH (newparts, lit);
      pos++;
    }
    if (pos) PUSH (newparts, 0);

    neg = 0;
    for (i = start; i < end; i++) {
      lit = parts[i];
      val = lglderef (globalgl, lit);
      if (val <= 0) continue;
      PUSH (newparts, lit);
      neg++;
    }
    if (neg) PUSH (newparts, 0);

    if (neg && pos) stats.splits.total++, stats.splits.single++;
  }
  DEL (parts, sizeparts);
  parts = newparts, numparts = numnewparts, sizeparts = sizenewparts;
  flush (); 
  delta = lglprocesstime () - delta;
  msg (2, "finished refinement in %.2f seconds", delta);
  stats.refine.time += delta;
}

static int checkbackbone (int cand) {
  double start = lglprocesstime (), delta;
  int res;
  stats.backbone.count++;
  assert (!lglfixed (globalgl, cand));
  assert ((stable[abs (cand)] < 0) == (cand < 0));
  msg (2, "checking whether assumption %d is unsatisfiable", -cand);
  lglsetopt (globalgl, "clim", clim);
  lglassume (globalgl, -cand);
  res = sat ();
  if (res == 10) refine ();
  else if (res == 20) flush (); 
  delta = lglprocesstime () - start;
  stats.backbone.time += delta;
  return res;
}

static void merge (int a, int b) {
  double delta = lglprocesstime ();
  stats.merge.count++;
  mergeaux (a, b);
  msg (2, "merged %d and %d", a, b);
  stats.merged++;
  flush ();
  delta = lglprocesstime () - delta;
  msg (2, "finished merge in %.2f seconds", delta);
  stats.merge.time += delta;
}

static void initmulti () {
  if (domulti ()) {
    int i;
    for (i = 0; i < MULTINIT; i++) multirefine ();
    msg (1, "initialization by %d multiple solutions finished", MULTINIT);
  } else msg (1, "initialization through multiple solutions disabled");
}

static void extract () {
  int a, b, res;
  lglsetprefix (globalgl, "c [mequick.extract] ");
  if (inconsistent) return;
  if (!initialized) return;
  assert (minclim <= maxclim);
  clim = minclim;
  while (!limhit () && getcandpair (&a, &b)) {
    if (!(res = implies (a, b))) inclim ();
    else if (res == 10) refine (), declim ();
    else if (!(res = implies (b, a))) inclim ();
    else if (res == 10) refine (), declim ();
    else merge (a, b), declim ();
    if (candbackbone (&a) && checkbackbone (a)) declim ();
    if (domulti ()) multirefine ();
    if (doreduce ()) reduce ();
    if (dosimp ()) simp ();
  }
}

/*------------------------------------------------------------------------*/

static void simplify () {
  int * mark, i, removedlits = 0;

  if (inconsistent) {
    simpclauses = numclauses - 1;
    return;
  }

  msg (1,
    "starting to simplify formula lightly at %.2f seconds",
    lglprocesstime ());

  assert (!simpclauses);
  NEW (mark, maxvar + 1);

  for (i = 0; i < numclauses; i++) {
    int * c = clauses[i], j, k, l, lit, satisfied = 0;
    k = 0;
    for (j = k; (lit = c[j]); j++) {
      int val = lglfixed (globalgl, lit), other;
      if (val > 0) { satisfied = 1; break; }
      if (val < 0) continue;
      other = chase (lit);
      val = mark [ abs (other) ];
      if (other < 0) val = -val;
      if (val > 0) continue;
      if (val < 0) { satisfied = 1; break; }
      mark [ abs (other) ] = other;
      c[k++] = other;
    }
    if (lit) {
      assert (satisfied);
      for (l = j + 1; c[l]; l++)
        ;
    } else assert (!satisfied), l = j;
    assert (!c[l]);

    for (j = 0; j < k; j++) mark [ abs (c[j]) ] = 0;

    if (satisfied) {
      DEL (c, l + 1);
      clauses[i] = 0;
      simpclauses++;
    } else {
      assert (!lit);
      assert (k <= l);
      if (k < l) {
	c[k] = 0;
	removedlits += l - k;
	c = resize (0, c, (l+1)*sizeof*c, (k+1)*sizeof*c);
	clauses[i] = c;
      }
    }
  }

  DEL (mark, maxvar + 1);

  msg (1,
    "removed %d clauses and %d literals in simplification",
    simpclauses, removedlits);
}

/*------------------------------------------------------------------------*/

typedef struct Prof { const char * name; double time; int count; } Prof;

#define PUSHPROF(NAME) \
do { \
  Prof prof; \
  prof.name = # NAME; \
  prof.time = stats.NAME.time; \
  prof.count = stats.NAME.count; \
  PUSH (profs, prof); \
} while (0);

static int cmprof (const void * p, const void * q) {
  Prof * a = (Prof *) p, * b = (Prof *) q;
  if (a->time < b->time) return 1;
  if (a->time > b->time) return -1;
  return strcmp (a->name, b->name);
}

static void prprof (double t) {
  int numprofs, sizeprofs, i, sorted;
  Prof * profs;
  double r;
  numprofs = sizeprofs = 0;
  profs = 0;
  PUSHPROF (backbone);
  PUSHPROF (bce);
  PUSHPROF (cand);
  PUSHPROF (implies);
  PUSHPROF (merge);
  PUSHPROF (multi);
  PUSHPROF (order);
  PUSHPROF (prep);
  PUSHPROF (reduce);
  PUSHPROF (refine);
  PUSHPROF (simp);
  qsort (profs, sorted = numprofs, sizeof*profs, cmprof);
  PUSHPROF (sat);
  PUSHPROF (unsat);
  PUSHPROF (unknown);
  PUSHPROF (solver);
  r = t;
  for (i = 0; i < numprofs; i++) {
    if (i == sorted) {
#if 0
      msg (1, "           %8.2f %3.0f%% ?", r, pcnt (r, t));
#endif
      msg (1, "==================================");
      msg (1, "           %8.2f 100%% total", t);
      msg (1, "");
    }
    if (i == numprofs - 1)
      msg (1, "----------------------------------");
    msg (1, "%10d %8.2f %3.0f%% %s",
      profs[i].count, profs[i].time, pcnt (profs[i].time, t), profs[i].name);
    if (i < sorted) r -= profs[i].time;
  }
  DEL (profs, sizeprofs);
}

/*------------------------------------------------------------------------*/

static void prstats () {
  double inside = lglsec (globalgl), process = lglprocesstime ();
  int sum;
  if (verbose > 1) lglstats (globalgl);
  msg (1, "");
  msg (1, "constructed %d = %d x %d models in %.2f seconds",
    stats.bpmodel.count * BPP, stats.bpmodel.count, BPP, stats.bpmodel.time);
  msg (1, "%d splits, %d single %.0f%%, %d multi %.0f%%",
    stats.splits.total,
    stats.splits.single, pcnt (stats.splits.single, stats.splits.total),
    stats.splits.multi, pcnt (stats.splits.multi, stats.splits.total));
  msg (1, "");
  msg (1, "spent %.2f seconds in SAT solver %.0f%%",
    inside, pcnt (inside, process));
  msg (1, "%lld conflicts, %lld decisions",
    (long long) lglgetconfs (globalgl),
    (long long) lglgetdecs (globalgl));
  msg (1, "");
  sum = stats.cands.rand + stats.cands.nonrand;
  msg (1, "%d candidate pairs, %d random %.0f%%, %d non-random %.0f%%",
    sum, 
    stats.cands.rand, pcnt (stats.cands.rand, sum),
    stats.cands.nonrand, pcnt (stats.cands.nonrand, sum));
  msg (1, "%d filled and %d dropped candidate lists",
    stats.filled, stats.dropped);
  msg (1, "%d fixed, %d equivalences, %d singletons",
    stats.fixed, stats.merged + stats.reprs, stats.singletons);

  msg (1, "");
  prprof (process);
}

/*------------------------------------------------------------------------*/

static void resetsighandlers () {
  (void) signal (SIGINT, sig_int_handler);
  (void) signal (SIGSEGV, sig_segv_handler);
  (void) signal (SIGABRT, sig_abrt_handler);
  (void) signal (SIGTERM, sig_term_handler);
  if (timelim) {

    alarm (0);		// TODO right way to cancel 'setitimer'?

    (void) signal (SIGPROF, sig_alrm_handler);
  }
}

static void caughtsigmsg (int sig) {
  msg (1, "");
  msg (1, "CAUGHT SIGNAL %d", sig);
  msg (1, "");
}

static void catchsig (int sig) {
  if (!catchedsig) {
    catchedsig = 1;
    caughtsigmsg (sig);
    prstats ();
    caughtsigmsg (sig);
  }
  resetsighandlers ();
  raise (sig);
}

static void catchalrm (int sig) { 
  assert (sig == SIGPROF);
  msg (1, "alarm signal at %.2f seconds", lglprocesstime ());
  (void) sig;
  timesup = 1;
}

static void setsighandlers () {
  sig_int_handler = signal (SIGINT, catchsig);
  sig_segv_handler = signal (SIGSEGV, catchsig);
  sig_abrt_handler = signal (SIGABRT, catchsig);
  sig_term_handler = signal (SIGTERM, catchsig);
}

static void setalarm () {
  struct itimerval newtimer;
  newtimer.it_interval.tv_usec = 0;
  newtimer.it_interval.tv_sec = 0;
  newtimer.it_value.tv_usec = 0;
  newtimer.it_value.tv_sec = timelim;
  setitimer (ITIMER_PROF, &newtimer, &oldtimer);
}

/*------------------------------------------------------------------------*/

static int lenclause (const int * c) {
  const int * p;
  for (p = c; *p; p++)
    ;
  return p - c;
}

static void delclause (int * c) {
  int len = lenclause (c) + 1;
  DEL (c, len);
}

static void reset () {
  int i;
  if (bcelgl) lglrelease (bcelgl);
  lglrelease (globalgl);
  globalgl = 0;
  DEL (clause, sizeclause);
  for (i = 0; i < numclauses; i++) {
    int * c = clauses[i];
    if (c) delclause (c);
  }
  DEL (clauses, sizeclauses);
  DEL (repr, maxvar + 1);
  DEL (part, maxvar + 1);
  DEL (stable, maxvar + 1);
  DEL (order, maxvar + 1);
  DEL (points, maxvar + 1);
  DEL (inactive, maxvar + 1);
  DEL (cared, maxvar + 1);
  DEL (vals, maxvar + 1);
  DEL (care, sizecare);
  DEL (parts, sizeparts);
  DEL (cands, sizecands);
  DEL (bbcands, sizebbcands);
  DEL (rcs, sizercs);
  assert (getenv ("MEQUICKLEAK") || !currentbytes);
  resetsighandlers ();
}

/*------------------------------------------------------------------------*/

int parsenumarg (const char * arg, const char * opt) {
  const char * p = arg;
  int res = 0, ch;
  ch = *p++;
  if (!ch) err ("empty string argument to '%s'", opt);
  res = ch - '0';
  while (isdigit (ch = *p++)) {
    int digit;
    if (INT_MAX/10 < res)
TOOLARGE:
      err ("argument to '%s' too large", opt);
    res *= 10;
    assert (res > 0);
    digit = ch - '0';
    if (INT_MAX - digit < res) goto TOOLARGE;
    res += digit;
    assert (res > 0);
  }
  if (ch) err ("invalid number in '%s %s'", opt, arg);
  assert (res > 0);
  return res;
}

#define U64_MAX ((~0ull)>>1)

int parseu64 (const char * arg, const char * opt) {
  unsigned long long res = 0;
  const char * p = arg;
  int ch;
  ch = *p++;
  if (!ch) err ("empty string argument to '%s'", opt);
  res = ch - '0';
  while (isdigit (ch = *p++)) {
    int digit;
    if (U64_MAX/10 < res)
TOOLARGE:
      err ("argument to '%s' too large", opt);
    res *= 10;
    assert (res > 0);
    digit = ch - '0';
    if (U64_MAX - digit < res) goto TOOLARGE;
    res += digit;
    assert (res > 0);
  }
  if (ch) err ("invalid unsigned 64 bit number in '%s %s'", opt, arg);
  assert (res > 0);
  return res;
}

int main (int argc, char ** argv) {
  int bins, units, reducedvars, reducedclauses, count;
  const char * inputpath = 0, * outputpath = 0;
  unsigned long long seed = 0;
  int closefile = 0;
  FILE * file;
  LDR * ldr;
  int i;
  for (i = 1; i < argc; i++) {
    if (!strcmp (argv[i], "-h")) {
      fprintf (stderr,
        "usage: mequick [<option> ...][<input> [<output>]]\n"
	"\n"
	"where <option> is one of the following\n"

	"\n"

	"  -h               print this command line option summary\n"
	"  -v               increase verbosity\n"
	"  -n               do not dump simplified formula\n"

	"\n"

	"  -s <seed>        random seed\n"
	"  --min <lim>      minimum conflict limit (default %d)\n"
	"  --max <lim>      maximum conflict limit (default %d)\n"

	"\n"

	"  -t <lim>         time limit in seconds\n"

	"\n"

	"  -c <path>        care file in DIMACS (enables preprocessing)\n"
	"  -a               append care file to output\n"

	"\n"

	"  -O0              zero preprocessing iterations\n"
	"  -O1 | -O         one preprocessing iteration\n"
	"  -O%d              %d preprocessing iterations (default)\n"
	"  -O<N>            <N> preprocessing iterations\n"

	"\n"

	"  --no-blocked     do not run BCE to extract reconstruction stack\n"
	"  --drop           drop candidates after merge/refinement\n"
	"  --no-fixed       do not use SAT solvers fixed literals\n"
	"  --no-multi       do not reconstruct multiple models\n"
	"  --reverse        try candidates in large partitions first\n"
	"  --no-rand-cand   do not randomize candidate selection\n"
	"  --no-rand-phase  do not randomize phase selection\n"
	"  --no-reduce      do not reduce cache size every 1000th SAT call\n"
	"  --no-repr        do not use SAT solvers internal union-find\n"
	"  --no-simp        do not use simplification every %dth SAT call\n"
	"  --stable         enable explicit back bone search\n"
	"  --no-order       do not reconstruct variable order\n"
	"  --force-order    even if not all clauses could eliminated\n"

	"\n"

	// TODO -O, -O1, ...

	"  <input>          in DIMACS format (default <stdin>)\n"
	"  <output>         in DIMACS format (default <stdout>)\n",
	MINCLIM, MAXCLIM, OPTDEF, OPTDEF, SIMPINT);
      exit (0);
    }
    else if (!strcmp (argv[i], "-v")) verbose++;
    else if (!strcmp (argv[i], "-n")) noutput = 1;
    else if (!strcmp (argv[i], "--no-blocked")) noblocked = 1;
    else if (!strcmp (argv[i], "--drop")) nodrop = 0;
    else if (!strcmp (argv[i], "--reverse")) reverse = 1;
    else if (!strcmp (argv[i], "--no-simp")) nosimp = 1;
    else if (!strcmp (argv[i], "--stable")) nostable = 0;
    else if (!strcmp (argv[i], "--no-repr")) norepr = 1;
    else if (!strcmp (argv[i], "--no-fixed")) nofixed = 1;
    else if (!strcmp (argv[i], "--no-multi")) nomulti = 1;
    else if (!strcmp (argv[i], "--no-rand-cand")) norandcand = 1;
    else if (!strcmp (argv[i], "--no-rand-phase")) norandphase = 1;
    else if (!strcmp (argv[i], "--no-reduce")) noreduce = 1;
    else if (!strcmp (argv[i], "--no-order")) norder = 1;
    else if (!strcmp (argv[i], "--force-order")) forceorder = 1;
    else if (!strcmp (argv[i], "-s")) {
      if (++i == argc) err ("argument to '-s' missing (try '-h')");
      seed = parseu64 (argv[i], "-s");
    } else if (!strcmp (argv[i], "-t")) {
      if (++i == argc) err ("argument to '-t' missing (try '-h')");
      timelim = parsenumarg (argv[i], "-t");
    } else if (!strcmp (argv[i], "--min")) {
      if (++i == argc) err ("argument to '--min' missing (try '-h')");
      minclim = parsenumarg (argv[i], "--min");
    } else if (!strcmp (argv[i], "--max")) {
      if (++i == argc) err ("argument to '--max' missing (try '-h')");
      maxclim = parsenumarg (argv[i], "--max");
    } else if (!strcmp (argv[i], "-c")) {
      if (carepath) err ("multiple '-c <path>' options");
      if (++i == argc) err ("argument to '-c' missing (try '-h')");
      carepath = argv[i];
    } else if (!strcmp (argv[i], "-a")) append = 1;
    else if (!strcmp (argv[i], "-O0")) optimize = 0;
    else if (!strcmp (argv[i], "-O")) optimize = 1;
    else if (argv[i][0] == '-' && argv[i][1] == 'O')
      optimize = parsenumarg (argv[i] + 2, "-O");
    else if (argv[i][0] == '-' && argv[i][1])
      err ("invalid command line option '%s' (try '-h')", argv[i]);
    else if (outputpath) err ("too many arguments (try '-h')");
    else if (inputpath) outputpath = argv[i];
    else inputpath = argv[i];
  }
  if (outputpath && noutput)
    err ("can not combine '-n' and '<output>'");
  if (verbose)
    lglbnr ("Mequick Magical Quick Equivalence Extractor",
      "c [mequick] ", stdout);
  if (minclim > maxclim)
    err ("minium conflict limit %d larger than maximum %d",
         minclim, maxclim);
  if (append && !carepath)
    err ("can not use '-a' without specifying '-c <path>'");
  if (append && noutput)
    err ("can not combine '-a' with '-n'");

  msg (1, "random seed %llu", (unsigned long long) seed);
  mysrand (seed);
  //
  // TODO explain with 'msg' more option settings ...

  if (timelim) {
    msg (1, "setting time limit to %d seconds", timelim);
    sig_alrm_handler = signal (SIGPROF, catchalrm);
    setalarm ();
  } else msg (1, "no time limit (set with '-t <lim>')");
  setsighandlers ();

  ldr = ldrminit (0, alloc, resize, dealloc);
  ldrsetadd (ldr, 0, add);
  ldrsetheader (ldr, 0, header);
  if (inputpath && strcmp (inputpath, "-")) ldrsetpath (ldr, inputpath);
  else ldrsetnamedfile (ldr, stdin, (inputpath = "<stdin>"));
  msg (1, "parsing %s", inputpath);
  if (!ldrparse (ldr)) {
    fprintf (stderr, "%s\n", ldrerr (ldr));
    exit (1);
  }
  ldrelease (ldr);
  msg (1, "finished parsing %d clauses after %.2f seconds.",
    numclauses, lglprocesstime ());

  init ();
  initblocked ();
  initorder ();
  preprocess ();
  initpart ();
  initmulti ();
  extract ();
  simplify ();

  reducedvars = bins = units = 0;
  for (i = 1; i <= maxvar; i++) {
    if (lglfixed (globalgl, i)) units++;
    else if (chase (i) != i) bins += 2;
    else reducedvars++;
  }

  reducedclauses = numclauses - simpclauses;
  assert (reducedclauses >= 0);

  msg (1, "");
  msg (1, "VARIABLES %d = %0.f%% OF %d",
    reducedvars, pcnt (reducedvars, maxvar), maxvar);
  msg (1, "");

  msg (1, "removed %d out of %d clauses %.0f%%",
    simpclauses, numclauses, pcnt (simpclauses, numclauses));

  msg (1, "thus %d original clauses remain %.0f%%",
    reducedclauses, numclauses, pcnt (reducedclauses, numclauses));

  msg (1, "will need %d additional binary clauses", bins);
  msg (1, "will need %d additional unit clauses", units);

  reducedclauses += bins + units;

  msg (1, "");
  msg (1, "CLAUSES %d = %0.f%% OF %d",
    reducedclauses, pcnt (reducedclauses, numclauses), numclauses);
  msg (1, "");

  if (!noutput) {

    if (!outputpath || !strcmp (outputpath, "-"))
      file = stdout, outputpath = "<stdout>";
    else if (!(file = fopen (outputpath, "w")))
      err ("can open '%s' for writing", outputpath);
    else closefile = 1;

    if (inconsistent) {
      msg (1, "writing one empty clause to '%s'", outputpath);
      fprintf (file, "p cnf 0 1\n0\n");
    } else {
      int actualvars = maxvar, actualclauses = reducedclauses;
      msg (1, "writing %d clauses to '%s'", reducedclauses, outputpath);

      if (append) {
	assert (carepath);
	if (actualvars < carevars) actualvars = carevars;
	actualclauses += careclauses;
      } 
      fprintf (file, "p cnf %d %d\n", actualvars, actualclauses);

      count = 0;

      for (i = 0; i < numclauses; i++) {
	const int * p, * c = clauses[i];
	int lit;
	if (!c) continue;
	for (p = c; (lit = *p); p++)
	  fprintf (file, "%d ", lit);
	fprintf (file, "0\n"), count++;
      }

      for (i = 1; i <= maxvar; i++) {
	int tmp;
	if ((tmp = lglfixed (globalgl, i))) {
	  fprintf (file, "%d 0\n", (tmp < 0) ? -i : i), count++;
	} else if ((tmp = chase (i)) != i) {
	  fprintf (file, "%d %d 0\n", -i, tmp), count++;
	  fprintf (file, "%d %d 0\n", i, -tmp), count++;
	}
      }

      assert (count == reducedclauses);

      if (append) {
	assert (carepath);
	msg (1, "appending %d clauses from '%s'", careclauses, carepath);
	for (i = 0; i < numcare; i++) {
	  int lit = care[i];
	  if (lit) fprintf (file, "%d ", lit);
	  else fputs ("0\n", file), count++;
	}
      }

      assert (count == actualclauses);
    }

    if (closefile) fclose (file);
  }

  prstats ();
  reset ();
  msg (1, "");
  msg (1, "%.2f seconds process time, %.1f MB maximally allocated",
    lglprocesstime (), maxbytes/(double)(1<<20));
  return 0;
}
