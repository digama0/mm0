#!/bin/sh
# Runs all tests. Run this from the tests/ directory;
# you need mm0-rs and mm0-c to be on your path.

set -euo pipefail

cd "$(dirname "$0")" || exit 1

escape=$(printf '\033')
red="$escape[0;31m"
green="$escape[0;32m"
cyan="$escape[0;36m"
white="$escape[0;97m"
bold="$escape[1m"
off="$escape[0m"

# set to 1 if any test fails
exit_code=0

run_test() {
  local cmd=$1 pfx=$2 dir=${3%/*} test=${3##*/} ext=$4 expect=$5
  local output status is_ok i

  echo -n "  test $pfx$dir/${white}$test${off}.$ext: "

  # Initialize status, run command, and capture exit code safely under 'set -e'
  status=0
  output=$($cmd "$dir/$test" 2>&1) || status=$?

  is_ok=0
  for i in $expect; do
    if [ "$status" -eq "$i" ]; then
      is_ok=1
      break
    fi
  done

  if [ "$is_ok" -eq 0 ]; then
    echo "${red}failed${off} (exit code = $status)"
    echo "---------------------------------------"
    echo "$output"
    echo "---------------------------------------"
    echo ""
    exit_code=1
  else
    echo "${green}ok${off}"
  fi
}

print_section() {
  echo "${cyan}--- $1 ---${off}"
}

# --- mm0_mmu section ---
if [ -d mm0_mmu ]; then
  cd mm0_mmu

  print_section "mm0_mmu: pass (mm0-rs)"
  for test in pass/*.mm0; do
    [ -e "$test" ] || continue
    run_test ./run-mm0-rs.sh mm0_mmu/ "${test%.*}" mm0 0
  done
  echo

  print_section "mm0_mmu: pass (mm0-hs)"
  for test in pass/*.mm0; do
    [ -e "$test" ] || continue
    run_test ./run-mm0-hs.sh mm0_mmu/ "${test%.*}" mm0 0
  done
  echo

  print_section "mm0_mmu: fail (mm0-rs)"
  for test in fail/*.mm0; do
    [ -e "$test" ] || continue
    run_test ./run-mm0-rs.sh mm0_mmu/ "${test%.*}" mm0 "1 2 255"
  done
  echo

  print_section "mm0_mmu: fail (mm0-hs)"
  for test in fail/*.mm0; do
    [ -e "$test" ] || continue
    run_test ./run-mm0-hs.sh mm0_mmu/ "${test%.*}" mm0 "1 2 255"
  done
  echo

  print_section "mm0_mmu: run (mm0-rs)"
  for test in run/*.mm0; do
    [ -e "$test" ] || continue
    run_test ./run-mm0-rs.sh mm0_mmu/ "${test%.*}" mm0 "0 1 2 255"
  done
  echo

  cd ..
fi

# --- mm1 section ---
if [ -d mm1 ]; then
  cd mm1

  print_section "mm1: pass (mm1-rs)"
  for test in pass/*.mm1; do
    [ -e "$test" ] || continue
    run_test ./run.sh mm1/ "${test%.*}" mm1 0
  done
  echo

  print_section "mm1: pass (mm1-hs)"
  for test in pass/*.mm1; do
    [ -e "$test" ] || continue
    run_test ./run-hs.sh mm1/ "${test%.*}" mm1 0
  done
  echo

  cd ..
fi

# --- mmb section ---
if [ -d mmb ]; then
  cd mmb

  print_section "mmb: run (mmb-rs)"
  for test in run/*.mmb; do
    [ -e "$test" ] || continue
    run_test ./run.sh mmb/ "${test%.*}" mmb "0 1 2 3 4 255"
  done
  echo

  cd ..
fi

exit $exit_code
