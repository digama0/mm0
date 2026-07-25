#!/bin/sh

set -euo pipefail

cd "$(dirname "$0")" || exit 1

MM0_RS="${MM0_RS:-mm0-rs}"
MM0_HS="${MM0_HS:-mm0-hs}"
MM0_C="${MM0_C:-mm0-c}"

# -------------------------
# Pre-flight checks
# -------------------------
for exe in "$MM0_RS" "$MM0_HS" "$MM0_C"; do
  if ! command -v "$exe" >/dev/null 2>&1; then
    echo "❌ Error: required executable '$exe' not found in PATH" >&2
    exit 1
  fi
done

echo "✅ All required executables found (rs, hs, c)"

# -------------------------
# helper: run test
# -------------------------
run_test() {
  name="$1"
  mm1="$2"
  mm0="$3"
  join_mm0="${4:-}"

  echo "=============================="
  echo "🧪 Testing: $name"
  echo "=============================="

  workdir="$(mktemp -d -t "mm0_${name}_XXXX")"
  echo "📁 Working dir: $workdir"

  rs_mmb="$workdir/rs.mmb"
  hs_mmb="$workdir/hs.mmb"

  # -------------------------
  # RS compile
  # -------------------------
  "$MM0_RS" compile "$mm1" "$rs_mmb"

  # -------------------------
  # HS compile (NO join support)
  # -------------------------
  "$MM0_HS" compile "$mm1" "$hs_mmb"

  # -------------------------
  # compare mmb outputs
  # -------------------------
  if ! cmp -s "$rs_mmb" "$hs_mmb"; then
    echo "❌ FAIL: RS and HS .mmb outputs differ for $name"
    echo "RS: $rs_mmb"
    echo "HS: $hs_mmb"
    exit 1
  fi

  echo "✅ RS == HS for .mmb"

  # -------------------------
  # mm0-c step (uses RS output)
  # -------------------------
  "$MM0_C" "$rs_mmb" < "$mm0"

  echo "✅ mm0-c passed for $name"

  # -------------------------
  # optional: join-based test (RS only)
  # -------------------------
  if [ -n "$join_mm0" ]; then
    echo "🔀 Join test (RS only)"

    joined="$workdir/joined.mm0"
    joined_mmb="$workdir/joined.mmb"

    "$MM0_RS" join "$mm0" > "$joined"
    "$MM0_RS" compile "$mm1" "$joined_mmb"

    "$MM0_C" "$joined_mmb" < "$joined"

    echo "✅ join test passed for $name"
  fi

  echo "🎉 SUCCESS: $name"
}

# -------------------------
# tests
# -------------------------

run_test "peano" "peano.mm1" "peano.mm0"

# Add more:
# run_test "peano_hex" "peano_hex.mm1" "peano_hex.mm0" "join"
# run_test "mm0" "mm0.mm1" "mm0.mm0" "join"
# run_test "x86" "x86.mm1" "x86.mm0" "join"