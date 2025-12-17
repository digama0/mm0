#!/bin/sh
# Runs all tests. Run this from the tests/ directory;
# you need mm0-rs and mm0-c to be on your path.

escape=$(printf '\033')
red="$escape[0;31m"
green="$escape[0;32m"
cyan="$escape[0;36m"
white="$escape[0;97m"
off="$escape[0m"

# set to 1 if any test fails
exit_code=0

run_test() {
  local cmd=$1 pfx=$2 dir=${3%/*} test=${3##*/} ext=$4 expect=$5 output status
  echo -n "test $pfx$dir/${white}$test${off}.$ext: "
  output=$($cmd $dir/$test 2>&1)
  status=$?
  local is_ok=0
  for i in $expect; do
    if [ $status -eq $i ]; then
      is_ok=1
    fi
  done
  if [ $is_ok -eq 0 ]; then
    echo "${red}failed${off} (exit code = $status)"; exit_code=1
    echo "---------------------------------------"
    echo "$output"
    echo "---------------------------------------\n"
  else
    echo "${green}ok${off}"
  fi
}

cd mm0_mmu
for test in pass/*.mm0; do
  run_test ./run-mm0-rs.sh mm0_mmu/ ${test%.*} mm0 0
done; echo
for test in fail/*.mm0; do
  run_test ./run-mm0-rs.sh mm0_mmu/ ${test%.*} mm0 "1 2 255"
done; echo
for test in run/*.mm0; do
  run_test ./run-mm0-rs.sh mm0_mmu/ ${test%.*} mm0 "0 1 2 255"
done; echo
cd ..

cd mm1
for test in pass/*.mm1; do
  run_test ./run.sh mm1/ ${test%.*} mm1 0
done; echo
cd ..

cd mmb
for test in run/*.mmb; do
  run_test ./run.sh mmb/ ${test%.*} mmb "0 1 2 3 4 255"
done; echo
cd ..

exit $exit_code
