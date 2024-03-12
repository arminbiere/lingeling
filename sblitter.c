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
#include <unistd.h>

/*------------------------------------------------------------------------*/

#include <sys/time.h>		// for 'setitimer' might be unportable ...

/*------------------------------------------------------------------------*/

#define OPTDEF 4

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

/*------------------------------------------------------------------------*/

typedef struct Clause Clause;
typedef struct LR LR;
typedef struct Prof Prof;
typedef struct Timer Timer;

/*------------------------------------------------------------------------*/

struct Clause {
  int size, local, blocked, satbyunits;
  unsigned hash;
  Clause * next;
  int * lits;
};

struct LR { int l, r; };

struct Prof { const char * name; double time; };

struct Timer { double start, * ptr; };

/*------------------------------------------------------------------------*/

static size_t currentbytes, maxbytes;

/*------------------------------------------------------------------------*/

static int * work, numwork, sizework;
static int * sizes, numsizes, sizesizes;
static int * clause, numclause, sizeclause;
static LR * lrs; static int numlrs, sizelrs;
static int numclauses, sizeclauses, localclauses, stamp;
static unsigned ** bitmaps, numbitmaps, sizebitmaps, sizebitmap;
static Clause ** hash; static unsigned sizehash;
static int bcelim, timelim, limhitreported;
static int lastblockedr, savedlastblockedr;
static int maxvar, speclauses;
static signed char * local;
static Clause ** clauses;

/*------------------------------------------------------------------------*/

static Timer * timers; static int numtimers, sizetimers;

static struct {
  int rounds;
  struct { int hits, subs; } cache;
  struct { int lookups, hits; } hash;
  struct { int total, explicit, implicit; } blocked;
  struct { int local, global; } clauses;
  struct { int bces, simps, full, partial; } calls;
  struct {
    double bce, full, partial;
    double first, units, large, quickdecompose, simp;
  } time;
} stats;

/*------------------------------------------------------------------------*/

static volatile sig_atomic_t timesup, catchedsig;
static struct itimerval oldtimer;

static void (*sig_int_handler)(int);
static void (*sig_segv_handler)(int);
static void (*sig_abrt_handler)(int);
static void (*sig_term_handler)(int);
static void (*sig_alrm_handler)(int);

/*------------------------------------------------------------------------*/

static int nosimp = 1, optimize = -1, verbose, noutput;
static int noquick, nounits, nolarge, nocache, noprior, forceunits;
static int noimplicit = 1, nosubset = 1, nolocal = 1, nofull = 1;
static int tryfirst = 0, trustfirst = 0;

/*------------------------------------------------------------------------*/

static void err (const char * fmt, ...) {
  va_list ap;
  fputs ("*** sblitter: ", stderr);
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  fflush (stderr);
  exit (1);
}

static FILE * msgfile;

static void msg (int level, const char * fmt, ...) {
  va_list ap;
  if (verbose < level) return;
  fputs ("c [sblitter] ", msgfile);
  va_start (ap, fmt);
  vfprintf (msgfile, fmt, ap);
  va_end (ap);
  fputc ('\n', msgfile);
  fflush (msgfile);
}

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

static void pushtimer (double * p) {
  double start = lglprocesstime ();
  Timer timer;
  timer.start = start;
  timer.ptr = p;
  PUSH (timers, timer);
}

static double poptimer () {
  Timer * timer;
  double delta;
  assert (numtimers);
  timer = timers + --numtimers;
  delta = lglprocesstime () - timer->start;
  if (timer->ptr) *timer->ptr += delta;
  return delta;
}

static void flushtimers () {
  while (numtimers) (void) poptimer ();
}

/*------------------------------------------------------------------------*/

static void header (void * dummy, int v, int c) {
  (void) dummy;
  maxvar = v;
  speclauses = c;
  msg (1, "found header 'p cnf %d %d'", v, c);
}

/*------------------------------------------------------------------------*/

static int cmplit (const void * p, const void * q) {
  return (*(int *) p) - *(int*) q;
}

static void sortclause () {
  assert (numclause > 0);
  assert (!clause[numclause-1]);
  qsort (clause, numclause - 1, sizeof *clause, cmplit);
}

static unsigned primes[] = {
2000000011u, 2000000033u, 2000000063u, 2000000087u, 2000000089u,
2000000099u, 2000000137u, 2000000141u, 2000000143u, 2000000153u,
};

static const unsigned numprimes = sizeof primes / sizeof *primes;

static unsigned hashclause () {
  unsigned res = 0;
  int i, j;
  j = 0;
  for (i = 0; i < numclause; i++) {
    res += primes[j++] * (unsigned) clause[i];
    if (j == (int) numprimes) j = 0;
  }
  return res;
}

static int sameclause (const int * c, const int * d) {
  for (;;) {
    int lit;
    if ((lit = *c++) != *d++) return 0;
    if (!lit) return 1;
  }
}

static Clause * findclause (const int * c) {
  int lit, size;
  Clause * res;
  unsigned h;
  stats.hash.lookups++;
  assert (!numclause);
  while ((lit = *c++)) PUSH (clause, lit);
  size = numclause;
  PUSH (clause, 0);
  sortclause ();
  h = hashclause () & (sizehash - 1);
  for (res = hash[h];
       res &&
	 size == res->size &&
	 !sameclause (res->lits, clause);
       res = res->next)
    ;
  numclause = 0;
  if (res) stats.hash.hits++;
  return res;
}

static void enlargehash () {
  Clause ** oldhash = hash, * p, * next;
  unsigned oldsize = sizehash, h, i;
  sizehash = oldsize ? 2 * oldsize : 1024;
  NEW (hash, sizehash);
  for (i = 0; i < oldsize; i++) {
    for (p = oldhash[i]; p; p = next) {
      next = p->next;
      h = p->hash & (sizehash - 1);
      p->next = hash[h];
      hash[h] = p;
    }
  }
  DEL (oldhash, oldsize);
}

static void insertclause (Clause * c) {
  Clause ** p;
  assert (!noimplicit);
  if (numclauses >= (int) sizehash) enlargehash ();
  c->hash = hashclause ();
  p = hash + (c->hash & (sizehash - 1));
  c->next = *p;
  *p = c;
}

static void add (void * dummy, int lit) {
  Clause * c;
  int i;
  (void) dummy;
  PUSH (clause, lit);
  if (lit) return;
  NEW (c, 1);
  NEW (c->lits, numclause);
  sortclause ();
  for (i = 0; i < numclause; i++) c->lits[i] = clause[i];
  c->size = numclause - 1;
  PUSH (clauses, c);
  if (!noimplicit) insertclause (c);
  numclause = 0;
  assert (noimplicit || findclause (c->lits));
}

/*------------------------------------------------------------------------*/

static int limhit () {
  if (limhitreported) return 1;
  if (timelim && timesup) {
    msg (1, "time limit hit after %.2f seconds", lglprocesstime ());
    limhitreported = 1;
    return 1;
  }
  if (bcelim && stats.calls.bces >= bcelim) {
    msg (1, "BCE call limit hit after %.2f seconds", lglprocesstime ());
    limhitreported = 1;
    return 1;
  }
  return 0;
}

/*------------------------------------------------------------------------*/

static void poke (unsigned * bm, int idx) {
  unsigned u, p, b;
  assert (0 <= idx);
  u = (unsigned) idx;
  p = u >> 5;
  assert (p < sizebitmap);
  b = u & 31;
  bm[p] |= 1u << b;
}

static unsigned * cache () {
  unsigned * bm;
  int i;
  assert (!nocache);
  NEW (bm, sizebitmap);
  for (i = 0; i < numclauses; i++)
    if (clauses[i]->blocked) poke (bm, i);
  return bm;
}

static int subset (unsigned a, unsigned b) { return !(a & ~b); }

static int cached () {
  unsigned * bm, i;
  int res;
  if (nocache) return 0;
  if (!numbitmaps) return 0;
  bm = cache ();
  res = 0;
  for (i = 0; !res && i < numbitmaps; i++) {
    unsigned * other = bitmaps[i], j;
    int subneeded = 0;
    res = 1;
    for (j = 0; res && j < sizebitmap; j++) {
      unsigned a = other[j], b = bm[j];
      if (a == b) continue;
      else if (nosubset) res = 0;
      else if ((res = subset (a, b))) subneeded = 1;
    }
    if (res) {
      if (subneeded) {
	stats.cache.subs++;
	msg (2, "cached bit-map %d is a super set", i);
      } else msg (2, "cached bit-map %d matches exactly", i);
      stats.cache.hits++;
    }
  }
  DEL (bm, sizebitmap);
  return res;
}

/*------------------------------------------------------------------------*/

static double maxmb () { return maxbytes/(double)(1<<20); }
static double avg (double a, double b) { return b ? a / b : 0; }
static double pcnt (double a, double b) { return avg (100*a, b); }

static double relblk () {
  return pcnt (stats.blocked.total, numclauses);
}

/*------------------------------------------------------------------------*/

static void incblockedexplicit () {
  stats.blocked.total++;
  stats.blocked.explicit++;
}

static void decblockedexplicit () {
  assert (stats.blocked.total > 0);
  assert (stats.blocked.explicit > 0);
  stats.blocked.total--;
  stats.blocked.explicit--;
}

/*------------------------------------------------------------------------*/

static int term (void * dummy) {
  (void) dummy;
  return timelim && timesup;
}

static int bce () {
  int res, i, full, ntrying, wasfull;
  double delta;
  if (limhit ()) return 0;
  stats.calls.bces++;
  if (cached ()) return 0;
  pushtimer (&stats.time.bce);
  msg (3, "starting BCE %d", stats.calls.bces);
  full = nolocal || (localclauses < stats.blocked.total/2);
  do {
    LGL * lgl = lglminit (0, alloc, resize, dealloc);
    double simpdelta;
    char prefix[80];
    int usedlocal = 0;
    stats.calls.simps++;
    assert (msgfile);
    lglsetout (lgl, msgfile);
    sprintf (prefix, "c [sbliter.bce%d] ", stats.calls.simps);
    lglsetprefix (lgl, prefix);
    lglsetopt (lgl, "plain", 1);
    lglsetopt (lgl, "block", 1);
    lglsetopt (lgl, "blkrtc", 1);
    lglsetopt (lgl, "blkclslim", INT_MAX);
    lglsetopt (lgl, "blkocclim", INT_MAX);
    lglsetopt (lgl, "verbose", verbose-1);
    lglsetopt (lgl, "wait", 0);
    lglseterm (lgl, term, 0);
    ntrying = 0;
    for (i = 0; i < numclauses; i++) {
      Clause * c = clauses[i];
      const int * p;
      int lit;
      if (!c->blocked) continue;
      if (!full && c->local) {
	 stats.clauses.local++;
	 usedlocal = 1;
      } else {
	if (c->blocked == stamp) ntrying++;
	stats.clauses.global++;
	for (p = c->lits; (lit = *p); p++) lgladd (lgl, lit);
	lgladd (lgl, 0);
      }
    }
    wasfull = full;
    if (!usedlocal) full = 1;
    pushtimer (0);
    res = lglsimp (lgl, 0);
    simpdelta = poptimer ();
    if (full) {
      stats.calls.full++;
      stats.time.full += simpdelta;
      msg (2, "full simplification %d (%.0f%% of %d) took %.2f sec",
        stats.calls.full,
	pcnt (stats.calls.full, stats.calls.simps),
	stats.calls.simps,
	simpdelta);
    } else {
      stats.calls.partial++;
      stats.time.partial += simpdelta;
      msg (2, "partial simplification (%d %.0f%% of %d) took %.2f sec",
        stats.calls.partial,
	pcnt (stats.calls.partial, stats.calls.simps),
	stats.calls.simps,
	simpdelta);
    }
    if (res == 20) res = 0;
    else if (!(res = !lglnclauses (lgl)) && ntrying > 1 && !noimplicit) {
      int * reconstkstart, *reconstktop, count = 0;
      const int * p, * next;
      lglreconstk (lgl, &reconstkstart, &reconstktop);
      for (p = reconstkstart; p < reconstktop; p = next + 1) {
	Clause * c = findclause (p);
	for (next = p; *next; next++)
	  ;
	if (!c) continue;
	if (c->blocked) {
	  if (c->blocked != stamp) continue;
	  decblockedexplicit ();
	  if (wasfull || !c->local) assert (ntrying > 0), ntrying--;
	}
	msg (3, "implicitly blocking clause of size %d", c->size);
	c->blocked = INT_MAX;
	stats.blocked.total++;
	stats.blocked.implicit++;
	count++;
      }
      if (count > 0) {
	int actualblocked = stats.blocked.total - ntrying;
	assert (actualblocked >= 0);
        msg (1, 
  "blocking %d implicitly at %.2f seconds, %d blocked %.0f%%, %.1f MB",
	  count, lglprocesstime (),
	  actualblocked, pcnt (actualblocked,  numclauses),
	  maxmb ());
      }
    }
    lglrelease (lgl);
  } while (res && !full++);
  delta = poptimer ();
  msg (3, "finished BCE %d in %.2f seconds result %d",
     stats.calls.bces, delta, res);
  if (!nocache && !res) {
    unsigned * bm = cache ();
    PUSH (bitmaps, bm);
  }
  return res;
}

/*------------------------------------------------------------------------*/

static void localize (void) {
  int i, numnonlocalvars = 0,  lit;
  const int * p;
  Clause * c;
  localclauses = 0;
  if (!local) NEW (local, maxvar + 1);
  for (i = 1; i <= maxvar; i++) local[i] = 1;
  for (i = 0; i < numclauses; i++) {
    c = clauses[i];
    if (c->blocked) continue;
    for (p = c->lits; (lit = *p); p++) {
      int idx = abs (lit);
      if (!local[idx]) continue;
      local[idx] = 0;
      numnonlocalvars++;
    }
  }
  msg (2, "found %d local variables %.0f%% and %d non-local variables %.0f%%",
    numnonlocalvars, pcnt (numnonlocalvars, maxvar),
    maxvar - numnonlocalvars, pcnt (maxvar - numnonlocalvars, maxvar));
  for (i = 0; i < numclauses; i++) {
    c = clauses[i];
    if (c->blocked) {
      for (p = c->lits; (lit = *p) && local[abs (lit)]; p++)
	;
      if (lit) c->local = 0;
      else c->local = 1, localclauses++;
    } else c->local = 0;
  }
  msg (2, "found %d local clauses %.0f%% out of %d blocked clauses %.0f%%",
    localclauses, pcnt (localclauses, stats.blocked.total),
    stats.blocked.total, pcnt (stats.blocked.total, numclauses));
}

/*------------------------------------------------------------------------*/

static void bceonfirst () {
  int i, ntrying, solvable, first, reallytrust;
  double delta;
  if (tryfirst) {
    msg (1, "trying to block first %d clauses", tryfirst);
    first = tryfirst;
  } else if (trustfirst) {
    msg (1, "assuming first %d clauses are blocked", trustfirst);
    first = trustfirst;
  } else {
    msg (1,
      "no first part to be tried or trusted (use '--{try,trust}-first')");
    return;
  }
  if (tryfirst) reallytrust = 0;
  else reallytrust = !stats.blocked.total;
  pushtimer (&stats.time.first);
  msg (2, "new stamp %d", ++stamp);
  ntrying = solvable = 0;
  assert (first > 0);
  for (i = 0; i < first; i++) {
    Clause * c = clauses[i];
    assert (c->blocked == INT_MAX || c->blocked < stamp);
    if (c->blocked) continue;
    c->blocked = stamp;
    incblockedexplicit ();
    ntrying++;
  }
  if (ntrying) {
    if (trustfirst && reallytrust) solvable = 1;
    else solvable = bce ();
    if (!solvable) {
      for (i = 0; i < first; i++) {
	Clause * c = clauses[i];
	if (c->blocked != stamp) continue;
	c->blocked = 0;
	decblockedexplicit ();
      }
    }
  }
  delta = poptimer ();
  if (!ntrying) {
    msg (1, "all first %d clauses already blocked", first);
  } else if (solvable) {
    lastblockedr = first;
    msg (1,
"blocking %d of first %d clauses in %.2f seconds, %d blocked %.0f%%, %.1f MB",
	ntrying, first, delta, stats.blocked.total, relblk (), maxmb ());
  } else {
    msg (1,
"removing %d first clauses does not produce BCE solvable CNF, %.02f seconds",
     ntrying, delta);
  }
}

/*------------------------------------------------------------------------*/

static void setsatbyunits () {
  int i, nsatisfied, npropunits, norigunits, res;
  LGL * propagator;
  msg (1, "computing propagated units and satisfied clauses");
  norigunits = 0;
  propagator = lglminit (0, alloc, resize, dealloc);
  lglsetprefix (propagator, "c [propagator] ");
  lglsetopt (propagator, "bca", 0);
  lglsetopt (propagator, "verbose", verbose);
  for (i = 0; i < numclauses; i++) {
    Clause * c = clauses[i];
    int lit, * p;
    if (c->size == 1) norigunits++;
    for (p = c->lits; (lit = *p); p++) lgladd (propagator, lit);
    lgladd (propagator, 0);
  }
  res = lglsimp (propagator, 1);
  msg (1, "ignoring propagator result %d after %.2f seconds",
    res, lglprocesstime ());
  npropunits = 0;
  for (i = 1; i <= maxvar; i++)
    if (lglfixed (propagator, i)) npropunits++;
  msg (1,
    "found %d units which is %.2f times original units %d",
    npropunits, avg (npropunits, norigunits), norigunits);
  nsatisfied = 0;
  for (i = 0; i < numclauses; i++) {
    Clause * c = clauses[i];
    int lit, *p, satisfied = 0;
    for (p = c->lits; !satisfied && (lit = *p); p++)
      if (lglfixed (propagator, lit) > 0) satisfied = 1;
    if (!satisfied) continue;
    nsatisfied++;
    c->satbyunits = 1;
  }
  lglrelease (propagator);
  msg (1, "determined %d top level satisfied clauses %.0f%% out of %d",
    nsatisfied, pcnt (nsatisfied, numclauses), numclauses);
}

static void bceunits () {
  int i, count = 0;
  if (limhit ()) return;
  if (!forceunits) {
    msg (1, 
      "forced inclusion of units disabled (use '--force-units' to enable)");
    return;
  }
  msg (2, "new stamp %d", ++stamp);
  for (i = 0; i < numclauses; i++) {
    Clause * c = clauses[i];
    assert (c->blocked == INT_MAX || c->blocked < stamp);
    if (c->size != 1) continue;
    c->blocked = stamp;
    incblockedexplicit ();
    count++;
  }
  if (!count) msg (1, "no unit-clause to included found");
  else msg (1, "forced inclusion of all %d unit clauses", count);
}

/*------------------------------------------------------------------------*/

static void bceononunits () {
  int i, count, ntrying, nunits, nsat, solvable;
  double delta;
  if (limhit ()) return;
  if (nounits) {
    msg (1, "trying BCE on non-unit clauses disabled");
    return;
  }
  pushtimer (&stats.time.units);
  setsatbyunits ();
  if (!nolocal) localize ();
  msg (2, "new stamp %d", ++stamp);
  count = ntrying = nunits = nsat = 0;
  msg (1, "trying BCE on non-unit clauses (disable with '--no-units')");
  savedlastblockedr = lastblockedr;
  for (i = 0; i < numclauses; i++) {
    Clause * c = clauses[i];
    assert (c->blocked == INT_MAX || c->blocked < stamp);
    if (c->satbyunits) { nsat++; continue; }
    if (c->size > 1) {
      count++;
      lastblockedr = i + 1;
      if (c->blocked) continue;
      c->blocked = stamp;
      incblockedexplicit ();
      ntrying++;
    } else if (c->size == 1) nunits++;
  }
  solvable = 0;
  if (!nunits && !nsat) msg (1, "no unblocked unit found");
  else if (!ntrying) msg (1, "no unblocked non-unit found");
  else {
    msg (2,
      "trying to block %d clauses out of %d without %d units",
      ntrying, count, nunits);
    solvable = bce ();
  }
  delta = poptimer ();
  if (solvable) {
    msg (1,
  "blocking %d non-unit clauses in %.2f seconds, %d blocked %.0f%%, %.1f MB",
      ntrying, delta, stats.blocked.total, relblk (), maxmb ());
  } else {
    msg (1,
      "removing %d units does not produce BCE solvable CNF, %.0f seconds",
      nunits, delta);
    lastblockedr = savedlastblockedr;
    for (i = 0; i < numclauses; i++) {
      Clause * c = clauses[i];
      if (c->size <= 1) continue;
      if (c->satbyunits) continue;
      assert (c->blocked == INT_MAX || c->blocked <= stamp);
      if (c->blocked != stamp) continue;
      decblockedexplicit ();
      c->blocked = 0;
    }
  }
}

/*------------------------------------------------------------------------*/

static void recordsize (int size) {
  assert (size >= 0);
  while (numsizes <= size) PUSH (sizes, 0);
  sizes[size] += 1;
}
  
static void bceononlarge () {
  int i, count, ntrying, nlarge, solvable, cutoffsize, sum;
  double delta;
  if (limhit ()) return;
  if (nolarge) {
    msg (1, "trying BCE on non-large clauses disabled");
    return;
  }
  pushtimer (&stats.time.large);
  msg (1, "trying BCE on non-large clauses (disable with '--no-large')");
  if (!nolocal) localize ();
  for (i = 0; i < numclauses; i++) {
    Clause * c = clauses[i];
    if (c->blocked) continue;
    recordsize (c->size);
  }
  sum = 0;
  for (cutoffsize = numsizes - 1; cutoffsize > 3; cutoffsize--) {
    int newsum = sum + sizes[cutoffsize];
    if (cutoffsize != numsizes - 1 && newsum > numclauses/2)
      break;				// max 50% // TODO option!
    sum = newsum;
  }
  for (i = numsizes-1; i >= 0; i--) {
    if (i == cutoffsize)
      msg (1, "---------------------------------- [ cut off size %d ] ----", i);
    if (sizes[i]) msg (1, "%10d clauses of size %5d", sizes[i], i);
  }
  if (numsizes <= 4) {
    msg (1, "only non-blocked clauses of size at most 3 found");
    (void) poptimer ();
    return;
  }
  msg (2, "new stamp %d", ++stamp);
  count = ntrying = nlarge = 0;
  savedlastblockedr = lastblockedr;
  for (i = 0; i < numclauses; i++) {
    Clause * c = clauses[i];
    if (c->size > cutoffsize) { nlarge++; continue; }
    count++;
    lastblockedr = i + 1;
    if (c->blocked) continue;
    c->blocked = stamp;
    incblockedexplicit ();
    ntrying++;
  }
  msg (1,
    "trying to block %d clauses of at most length %d ignoring %d",
     ntrying, cutoffsize, nlarge);
  solvable = bce ();
  delta = poptimer ();
  if (solvable) {
    msg (1,
"blocking %d non-large clauses in %.2f seconds, %d blocked %.0f%%, %.1f MB",
      ntrying, delta, stats.blocked.total, relblk (), maxmb ());
  } else {
    lastblockedr = savedlastblockedr;
    msg (1,
      "removing %d large clauses does not produce BCE solvable CNF",
      nlarge);
    for (i = 0; i < numclauses; i++) {
      Clause * c = clauses[i];
      if (c->size > cutoffsize) continue;
      if (c->blocked != stamp) continue;
      decblockedexplicit ();
      c->blocked = 0;
    }
  }
}

/*------------------------------------------------------------------------*/

static void pushlr (int l, int r) {
  LR lr;
  lr.l = l; lr.r = r;
  PUSH (lrs, lr);
}

static void quickdecomposestep (LR lr) {
  int i, m, l = lr.l, r = lr.r, ntrying = 0, ntrying1 = 0;
  assert (l <= r);
  if (l == r) return;
  if (limhit ()) return;
  if (!nolocal) localize ();
  msg (2, "trying to block [%d..%d]", l, r-1);
  msg (2, "new stamp %d", ++stamp);
  assert (stamp > 0);
  for (i = l; i < r; i++) {
    int cidx = work[i];
    Clause * c = clauses[cidx];
    if (c->blocked) continue;
    assert (!c->blocked);
    c->blocked = stamp;
    incblockedexplicit ();
    if (c->size == 1) ntrying1++;
    ntrying++;
  }
  savedlastblockedr = lastblockedr;
  lastblockedr = r;
  while (i < numclauses && clauses[i++]->blocked) lastblockedr = i;
  if (ntrying && bce ()) {
    msg (1,
      "blocking %d [%d..%d] %.2f sec, %d blocked %.0f%%, %.1f MB",
      ntrying, l, r-1, lglprocesstime (), stats.blocked.total, relblk (),
      maxmb ());
    if (ntrying1)
      msg (1, "from which %d are actual unit clauses", ntrying1);
  } else {
    int j = l;
    lastblockedr = savedlastblockedr;
    for (i = l ; i < r; i++) {
      int cidx = work[i];
      Clause * c = clauses[cidx];
      if (c->blocked != stamp) continue;
      work[j++] = cidx;
      decblockedexplicit ();
      c->blocked = 0;
    }
    if (j < r) {
      msg (2, "reduced [%d..%d[ of size %d to [%d..%d[ of size %d",
        l, r, r-l, l, j, j-l);
      r = j;
    } else assert (r == j);
    if (l + 1 < r) {
      m = l + (r - l + 1)/2;
      pushlr (m, r);
      pushlr (l, m);
    }
  }
}

static LR poplr () {
  int bestpos;
  LR lr;
  assert (numlrs > 0);
  if (!noprior)  {
    int best = lrs[bestpos = 0].r - lrs[0].l, i;
    for (i = 1; i < numlrs; i++) {
      int diff = lrs[i].r - lrs[i].l;
      if (diff < best) continue;
      if (diff == best && lrs[bestpos].l == lastblockedr) continue;
      bestpos = i;
      best = diff;
    }
  } else bestpos = numlrs-1;
  assert (0 <= bestpos && bestpos < numlrs);
  lr = lrs[bestpos];
  if (bestpos < --numlrs) lrs[bestpos] = lrs[numlrs];
  return lr;
}

static void quickdecompose (void) {
  int i, saved = stats.blocked.total, before;
  double delta;
  if (noquick) {
    msg (1, "quick decompose algorithm disabled");
    return;
  }
  pushtimer (&stats.time.quickdecompose);
  msg (1, "trying quick decompose algorithm (disable with '--no-quick')");
RESTART:
  stats.rounds++;
  before = stats.blocked.total;
  msg (1, "starting round %d of quick decompose", stats.rounds);
  for (i = 0; i < numclauses; i++) {
    Clause * c = clauses[i];
    if (c->blocked) continue;
    if (!c->size) continue;
    PUSH (work, i);
  }
  assert (!numlrs);
  pushlr (0, numwork);
  while (numlrs && !limhit ()) quickdecomposestep (poplr ());

  if (stats.blocked.total < numclauses && before < stats.blocked.total) {
    int blockedthisround = stats.blocked.total - before;
    msg (1,
      "blocked %d clauses in round %d of quick decompose after %.2f seconds",
      blockedthisround, stats.rounds, lglprocesstime ());
    if (!nofull && !limhit ()) goto RESTART;
  } else
    msg (1,
      "no clauses blocked in round %d of quick decompose after %.2f seconds",
      stats.rounds, lglprocesstime ());
       
  delta = poptimer ();
  assert (stats.blocked.total >= saved);
  msg (1,
  "quick decompose blocked %d clauses %.0f%% in %d rounds and %.2f seconds",
    stats.blocked.total - saved,
    pcnt (stats.blocked.total - saved, numclauses),
    stats.rounds, delta);
}

/*------------------------------------------------------------------------*/

#define PUSHPROF(NAME) \
do { \
  Prof prof; \
  prof.name = # NAME; \
  prof.time = stats.time.NAME; \
  PUSH (profs, prof); \
} while (0);

static int cmprof (const void * p, const void * q) {
  Prof * a = (Prof *) p, * b = (Prof *) q;
  if (a->time < b->time) return 1;
  if (a->time > b->time) return -1;
  return strcmp (a->name, b->name);
}

static void prprof () {
  int numprofs, sizeprofs, i;
  Prof * profs;
  double t, r;
  numprofs = sizeprofs = 0;
  profs = 0;
  PUSHPROF (units);
  PUSHPROF (first);
  PUSHPROF (large);
  PUSHPROF (quickdecompose);
  PUSHPROF (simp);
  qsort (profs, numprofs, sizeof*profs, cmprof);
  t = lglprocesstime ();
  r = t;
  for (i = 0; i < numprofs; i++) {
    msg (1, "%8.2f %3.0f%% %s",
      profs[i].time, pcnt (profs[i].time, t), profs[i].name);
    r -= profs[i].time;
  }
  msg (1, "%8.2f %3.0f%% unknown", r, pcnt (r, t));
  msg (1, "------------------------------");
  msg (1, "%8.2f 100%% total", t);
  DEL (profs, sizeprofs);
}

/*------------------------------------------------------------------------*/

static void prstats () {
  flushtimers ();
  msg (1, "%d BCE calls, average time %.2f seconds per call",
    stats.calls.bces, avg (stats.time.bce, stats.calls.bces));
  msg (1, "%d quick decompose rounds", stats.rounds);
  if (!noimplicit) {
    msg (1, "%d explicitly blocked %.0f%%, %d implicitly blocked %.0f%%",
      stats.blocked.explicit,
	pcnt (stats.blocked.explicit, stats.blocked.total),
      stats.blocked.implicit,
	pcnt (stats.blocked.implicit, stats.blocked.total));
    msg (1, "%d hash lookups, %d mapped back, %.0f%% hit rate",
      stats.hash.lookups, stats.hash.hits,
      pcnt (stats.hash.hits, stats.hash.lookups));
  }
  msg (1, "%d clauses tried, %.1f per actual simplification",
    stats.clauses.global, avg (stats.clauses.global, stats.calls.simps));
  if (!nolocal) {
    msg (1, "%d local clauses skipped %.0f%%, %.1f per actual simplification",
      stats.clauses.local,
      pcnt (stats.clauses.local, stats.clauses.local + stats.clauses.global),
      avg (stats.clauses.local, stats.calls.simps));
    msg (1, "%d partial simplifications %.0f%% using %.2f seconds %.0f%%",
      stats.calls.partial, 
      pcnt (stats.calls.partial, stats.calls.simps),
      stats.time.partial,
      pcnt (stats.time.partial, stats.time.bce));
    msg (1, "%d full simplifications %.0f%% using %.2f seconds %.0f%%",
      stats.calls.full, 
      pcnt (stats.calls.full, stats.calls.simps),
      stats.time.full,
      pcnt (stats.time.full, stats.time.bce));
  }
  if (!nocache) {
    size_t cachebytes = numbitmaps * sizebitmap * 4;
    msg (1, "%u bit-maps in cache %.1f MB %.0f%%",
      numbitmaps, cachebytes/(double)(1<<20), pcnt (cachebytes, maxbytes));
    msg (1, "%d cache hits results in %.2f%% cache hit rate",
      stats.cache.hits, pcnt (stats.cache.hits, stats.calls.bces));
    if (!nosubset)
      msg (1, "%d sub-set checks needed %.2f%%",
        stats.cache.subs, pcnt (stats.cache.subs, stats.cache.hits));
  }
  msg (1, "");
  prprof ();
  msg (1, "");
  msg (1, "%.2f seconds, %.1f MB maximally",
    lglprocesstime (), maxmb ());
}

/*------------------------------------------------------------------------*/

static void resetsighandlers () {
  (void) signal (SIGINT, sig_int_handler);
  (void) signal (SIGSEGV, sig_segv_handler);
  (void) signal (SIGABRT, sig_abrt_handler);
  (void) signal (SIGTERM, sig_term_handler);
  if (timelim) {
    alarm (0);
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
  timesup = 1;
  (void) sig;
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

static void reset () {
  int i;
  if (local) DEL (local, maxvar + 1);
  DEL (hash, sizehash);
  DEL (clause, sizeclause);
  for (i = 0; i < numclauses; i++) {
    Clause * c = clauses[i];
    DEL (c->lits, c->size + 1);
    DEL (c, 1);
  }
  DEL (clauses, sizeclauses);
  DEL (work, sizework);
  DEL (sizes, sizesizes);
  for (i = 0; i < (int) numbitmaps; i++) {
    unsigned * bm = bitmaps[i];
    DEL (bm, sizebitmap);
  }
  DEL (bitmaps, sizebitmaps);
  DEL (lrs, sizelrs);
  DEL (timers, sizetimers);
  resetsighandlers ();
  assert (getenv ("SBLITTERLEAK") || !currentbytes);
}

/*------------------------------------------------------------------------*/

int parseposnumarg (const char * arg, const char * opt) {
  const char * p = arg;
  int res = 0, ch;
  ch = *p++;
  if (!ch) err ("empty string argument to '%s'", opt);
  res = ch - '0';
  if (!res) err ("argument '%s' of '%s' starts with '0'", arg, opt);
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
  if (ch) err ("invalid positive number in '%s %s'", opt, arg);
  assert (res > 0);
  return res;
}

static void dump (int remaining, FILE * file) {
  int i;
  if (remaining || nosimp) {
    fprintf (file, "p cnf %d %d\n", maxvar,
      remaining ? (numclauses - stats.blocked.total) : stats.blocked.total);
    for (i = 0; i < numclauses; i++) {
      Clause * c = clauses[i];
      const int * p;
      int lit;
      if (!c->blocked == !remaining) continue;
      for (p = c->lits; (lit = *p); p++)
	fprintf (file, "%d ", lit);
      fprintf (file, "0\n");
    }
  } else {
    double delta;
    pushtimer (&stats.time.simp);
    int n;
    LGL * lgl;
    msg (1, "using Lingeling as simplifier on blocked part");
    localize ();
    lgl = lglminit (0, alloc, resize, dealloc);
    assert (msgfile);
    lglsetout (lgl, msgfile);
    lglsetprefix (lgl, "c [sblitter.simp] ");
    if (verbose > 1) lglsetopt (lgl, "verbose", verbose-1);
    lglsetopt (lgl, "bca", 0);
    for (i = 0; i < numclauses; i++) {
      Clause * c = clauses[i];
      const int * p;
      int lit;
      if (!c->blocked) continue;
      for (p = c->lits; (lit = *p); p++) lgladd (lgl, lit);
      lgladd (lgl, 0);
    }
    for (i = 1; i <= maxvar; i++)
      if (!local[i]) lglfreeze (lgl, i);

    msg (1, "simplifying blocked part with Lingeling %d times", optimize);
    (void) lglsimp (lgl, optimize);
    (void) limhit ();			// report time limit ...
    delta = poptimer ();
    if (verbose > 1) lglstats (lgl);
    n = lglnclauses (lgl);
    msg (1, "");
    msg (1,
      "SIMPLIFIED TO %d OUT OF %d CLAUSES %.0f%% IN %.2f SECONDS", 
      n, pcnt (n, stats.blocked.total), stats.blocked.total, delta);
    msg (1, "");
    lglprintall (lgl, file);
    lglrelease (lgl);
  }
}

int main (int argc, char ** argv) {
  const char * inputpath = 0, * blockedpath = 0, * remainingpath = 0;
  int i, closefile = 0, remaining = 0;
  FILE * file;
  LDR * ldr;
  msgfile = stdout;
  for (i = 1; i < argc; i++) {
    if (!strcmp (argv[i], "-h")) {
      assert (OPTDEF > 1);
      fprintf (stderr,
        "usage: sblitter [<option> ...][<input> [<blocked> [<remaining>]]]\n"
	"\n"
	"where <option is one of the following\n"
	"\n"
	"  -h             print this command line option summary\n"
	"  -v             increase verbosity\n"
	"  -r             dump remaining instead blocked clauses\n"
	"  -n             do not dump blocked nor remaining clauses\n"

	"\n"             

	"--try-first <L>  try to eliminated first <L> clauses\n"
	"--trust-first <L>  assume first <L> clauses blocked\n"

	"\n"             

	"  -t <lim>       time limit in seconds\n"
	"  -c <lim>       call limit in number of BCE calls\n" 

	"\n"             

	"  --simp         simplify with Lingeling before writing\n"
	"  -O0            zero simplification iterations\n"
	"  -O1 | -O       one simplification iteration\n"
	"  -O%d            %d simplification iterations (default)\n"
	"  -O<N>          <N> simplification iterations\n"
	"\n"

	"  --no-cache     disable caching of BCE calls\n"
	"  --no-large     do not try BCE on non-large clauses\n"
	"  --no-prior     use simple DFS instead of prioritized DFS\n"
	"  --no-quick     disable quick decompose algorithm\n"
	"  --no-units     do not try BCE on non-unit clauses\n"

	"\n"

	"  --full         run quick decompose until fix-point\n"
	"  --implicit     enable implicit destructive blocking\n"
	"  --local        enable local variable optimization\n"
	"  --subset       enable subset caching for BCE calls\n"

	"\n"

	"and input and output are specified as follows\n"
	"\n"
	"  <input>        input DIMACS file (default <stdin>)\n"
	"  <blocked>      blocked clauses (default <stdout>)\n"
	"  <remaining>    remaining clauses\n"
	"\n"
	"If <input> has a '.gz' or '.bz2' suffix it is tried to be\n"
	"decompressed during parsing using 'gunzip -c' or 'bzcat'.\n",
	OPTDEF, OPTDEF);
      exit (0);
    }
    else if (!strcmp (argv[i], "-v")) verbose++;
    else if (!strcmp (argv[i], "-r")) remaining = 1;
    else if (!strcmp (argv[i], "-n")) noutput = 1;

    else if (!strcmp (argv[i], "--try-first")) {
      if (++i == argc) err ("argument to '--try-first' missing (try '-h')");
      tryfirst = parseposnumarg (argv[i], "--try-first");
    } else if (!strcmp (argv[i], "--trust-first")) {
      if (++i == argc) err ("argument to --trust-first' missing (try '-h')");
      trustfirst = parseposnumarg (argv[i], "--trust-first");
    }

    else if (!strcmp (argv[i], "--simp")) nosimp = 0;
    else if (!strcmp (argv[i], "-O0")) optimize = 0, nosimp = 0;
    else if (!strcmp (argv[i], "-O")) optimize = 1, nosimp = 0;
    else if (argv[i][0] == '-' && argv[i][1] == 'O') {
      optimize = parseposnumarg (argv[i] + 2, "-O");
      nosimp = 0;
    }

    else if (!strcmp (argv[i], "--no-cache")) nocache = 1;
    else if (!strcmp (argv[i], "--implicit")) noimplicit = 0;
    else if (!strcmp (argv[i], "--no-large")) nolarge = 1;
    else if (!strcmp (argv[i], "--full")) nofull = 0;
    else if (!strcmp (argv[i], "--local")) nolocal = 0;
    else if (!strcmp (argv[i], "--no-prior")) noprior = 1;
    else if (!strcmp (argv[i], "--no-quick")) noquick = 1;
    else if (!strcmp (argv[i], "--subset")) nosubset = 0;
    else if (!strcmp (argv[i], "--no-units")) nounits = 1;
    else if (!strcmp (argv[i], "--force-units")) forceunits = 1;

    else if (!strcmp (argv[i], "-t")) {
      if (++i == argc) err ("argument to '-t' missing (try '-h')");
      timelim = parseposnumarg (argv[i], "-t");
    } else if (!strcmp (argv[i], "-c")) {
      if (++i == argc) err ("argument to '-c' missing (try '-h')");
      bcelim = parseposnumarg (argv[i], "-c");
    } else if (argv[i][0] == '-' && argv[i][1])
      err ("invalid command line option '%s' (try '-h')", argv[i]);
    else if (remainingpath) err ("too many arguments (try '-h')");
    else if (blockedpath) remainingpath = argv[i];
    else if (inputpath) blockedpath = argv[i];
    else inputpath = argv[i];
  }
  if (blockedpath && noutput)
    err ("can not combine '-n' and '<output>'");
  if (remaining && noutput)
    err ("can not combine '-n' and '-r'");
  if (remaining && remainingpath)
  if (nocache && nosubset)
    err ("can not combine '--no-cache' and '--no-sub'");
  if (noprior && noquick)
    err ("can not combine '--no-quick' and '--no-prior'");
#if 0
  if (nosimp && noutput)
    err ("can not combine '--no-simp' and '--no-output");
  if (nosimp && optimize >= 0)
    err ("can not combine '--no-simp' with '-O<N>'");
  if (optimize >= 0 && remaining)
    err ("can not combine '-r' with '-O<N>'");
#endif
  if (trustfirst && tryfirst)
    err ("can not combined '--try-first' and '--trust-first'");
  if (optimize < 0) optimize = OPTDEF;
  if (verbose)
    lglbnr ("Sblitter for CNF Blocked Clause Decomposition",
      "c [sblitter] ", msgfile);
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
  msg (1, "finished parsing %d clauses after %.2f seconds",
    numclauses, lglprocesstime ());
  if (timelim) {
    msg (1, "setting time limit to %d seconds", timelim);
    sig_alrm_handler = signal (SIGPROF, catchalrm);
    setalarm ();
  } else msg (1, "no time limit (set with '-t <lim>')");
  if (bcelim)
    msg (1, "setting BCE call limit to %d calls", bcelim);
  else
    msg (1, "no BCE call limit (set with '-c <lim>')");
  if (noprior)
    msg (1, "will use non-prioritized DFS in quick-decompose");
  else
    msg (1, "will use prioritized DFS in quick-decompose");
  sizebitmap = (numclauses + 31)/32;
  if (nocache) msg (1, "caching of BCE calls disabled");
  else {
    msg (1, "caching of BCE calls enabled (disable with '--no-cache')");
    msg (1, "each bit-map in BCE calls cache needs %u words (%u bytes)",
      sizebitmap, (sizebitmap*4));
  }
  if (!noutput) {
    if (nosimp)
      msg (1, "will not pass blocked part through Lingeling (enable with '--simp')");
    else msg (1, "will simplify blocked part %d times", optimize);
  }
  bceunits ();
  bceononunits ();
  bceonfirst ();
  bceononlarge ();
  quickdecompose ();
#ifndef NDEBUG
  {
    int count = 0;
    for (i = 0; i < numclauses; i++)
      if (clauses[i]->blocked) count++;
    assert (count == stats.blocked.total);
  }
#endif
  {
    int remaining = numclauses - stats.blocked.total;
    msg (1, "");
    msg (1,
      "BLOCKED %d OUT OF %d CLAUSES %.0f%%, %d REMAIN %.0f%%",
      stats.blocked.total, numclauses, pcnt (stats.blocked.total, numclauses),
      remaining, pcnt (remaining, numclauses));
    msg (1, "");
  }

  if (!noutput) {

    if (!blockedpath || !strcmp (blockedpath, "-"))
      file = stdout, blockedpath = "<stdout>";
    else if (!(file = fopen (blockedpath, "w")))
      err ("can open '%s' for writing", blockedpath);
    else closefile = 1;

    if (remaining)
      msg (1, "writing %d remaining clauses to '%s'",
	numclauses - stats.blocked.total, blockedpath);
    else
      msg (1, "writing %d blocked clauses to '%s'",
	stats.blocked.total, blockedpath);

    dump (remaining, file);

    if (closefile) fclose (file);

    if (remainingpath) {

      if (!strcmp (remainingpath, "-")) file = stdout;
      else if (!(file = fopen (remainingpath, "w")))
	err ("can open '%s' for writing", remainingpath);
      else closefile = 1;

      msg (1, "writing %d remaining clauses to '%s'",
	numclauses - stats.blocked.total, remainingpath);

      dump (1, file);

      if (closefile) fclose (file);
    }
  }

  reset ();
  prstats ();
  return 0;
}
