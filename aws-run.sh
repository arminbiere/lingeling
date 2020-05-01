if [[ "${COMP_S3_PROBLEM_PATH}" == *".xz" ]]; then
  aws s3 cp s3://${S3_BKT}/${COMP_S3_PROBLEM_PATH} supervised-scripts/test.cnf.xz
  unxz supervised-scripts/test.cnf.xz
else
  aws s3 cp s3://${S3_BKT}/${COMP_S3_PROBLEM_PATH} supervised-scripts/test.cnf
fi
/lingeling/plingeling supervised-scripts/test.cnf -t ${NUM_PROCESSES}
