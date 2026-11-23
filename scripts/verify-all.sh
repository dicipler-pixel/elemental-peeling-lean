#!/usr/bin/env bash
# Verify the whole record: every Lean file compiles, every theorem's axioms are within the
# three standard ones, every Lean citation in results/*.md resolves, and every measured number
# quoted in the fission theorem is reproducible.  Usage: bash scripts/verify-all.sh
set -uo pipefail
mkdir -p .scratch/verify
fail=0

echo "== Lean files"
for f in results/*.lean; do
  name=$(basename "$f" .lean)
  if lean "$f" > ".scratch/verify/$name.log" 2>&1; then
    n=$(grep -c '^theorem' "$f")
    printf "  %-34s compiles, %2d theorems\n" "$f" "$n"
  else
    printf "  %-34s FAILS TO COMPILE\n" "$f"; sed -n '1,5p' ".scratch/verify/$name.log"; fail=1; continue
  fi
  # axiom report
  ns=$(grep -o '^namespace [A-Za-z_0-9]*' "$f" | head -1 | awk '{print $2}')
  { cat "$f"; grep -o "^theorem [A-Za-z_0-9']*" "$f" | sed 's/theorem //' | sed "s/^/#print axioms $ns./"; } \
    > ".scratch/verify/ax_$name.lean"
  lean ".scratch/verify/ax_$name.lean" > ".scratch/verify/ax_$name.log" 2>&1
  bad=$(grep -E "sorryAx|sorry|native_decide" ".scratch/verify/ax_$name.log" | head -3)
  extra=$(grep -o "axioms: \[[^]]*\]" ".scratch/verify/ax_$name.log" \
          | sed 's/axioms: \[//;s/\]//' | tr ',' '\n' | sed 's/^ *//' \
          | grep -v -E '^propext$|^Classical.choice$|^Quot.sound$|^$' | sort -u)
  if [ -n "$bad" ] || [ -n "$extra" ]; then
    printf "  %-34s AXIOM PROBLEM\n" "$f"; [ -n "$bad" ] && echo "$bad"; [ -n "$extra" ] && echo "  extra: $extra"
    fail=1
  else
    printf "  %-34s axioms ⊆ {propext, Classical.choice, Quot.sound}, no sorry\n" "$f"
  fi
done

echo "== Citations"
if python3 scripts/check-lean-citations.py | tail -1 | grep -q "all Lean citations resolve"; then
  echo "  all Lean names cited in results/*.md resolve"
else
  echo "  BROKEN CITATIONS"; python3 scripts/check-lean-citations.py | tail -5; fail=1
fi

echo "== Random inputs"
if python3 scripts/random_laws.py 5000 > .scratch/verify/random.log 2>&1; then
  echo "  $(grep -c '^  ok' .scratch/verify/random.log) property groups on random inputs, 0 failed"
else
  echo "  PROPERTY FAILURES"; grep FAIL .scratch/verify/random.log | head -5; fail=1
fi
if python3 scripts/random_lean_cross.py 200 > .scratch/verify/cross.log 2>&1; then
  echo "  Lean vs the reference implementation: $(grep 'agree' .scratch/verify/cross.log | head -1)"
else
  echo "  LEAN CROSS-CHECK FAILED"; tail -5 .scratch/verify/cross.log; fail=1
fi

echo "== Counts (the four count formulas)"
if python3 scripts/count_formulas.py 1e6 > .scratch/verify/counts.log 2>&1 \
   && grep -q "COUNT CHECKS PASSED" .scratch/verify/counts.log; then
  echo "  $(grep 'COUNT CHECKS PASSED' .scratch/verify/counts.log | sed 's/^  //')"
else
  echo "  COUNT CHECKS FAILED"; tail -5 .scratch/verify/counts.log; fail=1
fi
if python3 scripts/base_key_zeros.py 1e7 1e3 4000 > .scratch/verify/basekey.log 2>&1 \
   && grep -q "BASE-KEY ZEROS PASSED" .scratch/verify/basekey.log; then
  echo "  $(grep 'BASE-KEY ZEROS PASSED' .scratch/verify/basekey.log | sed 's/^  //')"
else
  echo "  BASE-KEY ZERO CHECK FAILED"; tail -5 .scratch/verify/basekey.log; fail=1
fi

echo "== Specific heat (triangle, Dulong-Petit, table labels)"
if python3 scripts/specific_heat_bridge.py 20000 > .scratch/verify/heat.log 2>&1 \
   && grep -q "SPECIFIC HEAT BRIDGE PASSED" .scratch/verify/heat.log; then
  echo "  $(grep -c 'ok$' .scratch/verify/heat.log) triangle/DP/exchange groups ok, $(grep 'kappa =' .scratch/verify/heat.log | sed 's/^  //')"
  grep 'labels:' .scratch/verify/heat.log | sed 's/^/  /'
else
  echo "  SPECIFIC HEAT BRIDGE FAILED"; tail -5 .scratch/verify/heat.log; fail=1
fi

echo "== Random tests of the count relations"
if python3 scripts/random_count_relations.py 2000 1e8 > .scratch/verify/random_counts.log 2>&1 \
   && grep -q "RANDOM COUNT RELATIONS PASSED" .scratch/verify/random_counts.log; then
  echo "  $(grep 'RANDOM COUNT RELATIONS PASSED' .scratch/verify/random_counts.log | sed 's/^  //')"
else
  echo "  RANDOM COUNT RELATIONS FAILED"; grep FAIL .scratch/verify/random_counts.log | head -5; fail=1
fi

echo "== The one equation (results/one-equation.md)"
if python3 scripts/one_equation_check.py > .scratch/verify/oneeq.log 2>&1 \
   && grep -q "ONE-EQUATION CHECK PASSED" .scratch/verify/oneeq.log; then
  echo "  $(grep 'predicted span' .scratch/verify/oneeq.log | sed 's/^  //')"
  echo "  $(grep 'bin-mean (300 bins)' .scratch/verify/oneeq.log | sed 's/^  //')"
else
  echo "  ONE-EQUATION CHECK FAILED"; tail -4 .scratch/verify/oneeq.log; fail=1
fi

echo "== Reliability of the one equation, and configurations against data"
if python3 scripts/reliability.py 1e9 1000 > .scratch/verify/rel.log 2>&1 \
   && grep -q "RELIABILITY PASSED" .scratch/verify/rel.log; then
  echo "  $(grep 'RELIABILITY' .scratch/verify/rel.log | sed 's/^  //')"
  echo "  $(grep 'equal-size windows' .scratch/verify/rel.log | sed 's/^  //')"
else
  echo "  RELIABILITY FAILED"; tail -4 .scratch/verify/rel.log; fail=1
fi
if python3 scripts/element_configs.py > .scratch/verify/configs.log 2>&1 \
   && grep -q "CONFIG-vs-DATA CHECK PASSED" .scratch/verify/configs.log; then
  echo "  $(grep 'C/3R  ' .scratch/verify/configs.log | sed 's/^  //')"
  echo "  $(grep 'within block f' .scratch/verify/configs.log | sed 's/^  //')"
else
  echo "  CONFIG-vs-DATA CHECK FAILED"; tail -4 .scratch/verify/configs.log; fail=1
fi

echo "== The Light Table (digits 1, 3, 7, 9)"
if python3 scripts/digit_table.py 1e9 > .scratch/verify/digits.log 2>&1 \
   && grep -q "DIGIT TABLE BUILD PASSED" .scratch/verify/digits.log \
   && python3 scripts/light_table_figure.py > /dev/null 2>&1; then
  echo "  $(grep 'to 1e9' .scratch/verify/digits.log | sed 's/^  //')"
  echo "  $(grep -A1 'per digit' .scratch/verify/digits.log | tail -1 | sed 's/^  //')"
  echo "  figure: results/light-table.png ($(stat -c%s results/light-table.png) bytes)"
else
  echo "  DIGIT TABLE FAILED"; tail -4 .scratch/verify/digits.log; fail=1
fi

echo "== Class from the digit sequences"
if python3 scripts/class_from_digits.py 1e9 > .scratch/verify/classdig.log 2>&1 \
   && grep -q "CLASS-FROM-DIGITS PASSED" .scratch/verify/classdig.log; then
  echo "  $(grep 'air % 30 == class' .scratch/verify/classdig.log | sed 's/^  //')"
  echo "  $(grep 'segments checked' .scratch/verify/classdig.log | sed 's/^  //')"
else
  echo "  CLASS-FROM-DIGITS FAILED"; tail -4 .scratch/verify/classdig.log; fail=1
fi

echo "== Kindling against segments, and the elements' holes"
if python3 scripts/kindling_segments.py 1e9 > .scratch/verify/kindling.log 2>&1 \
   && grep -q "KIND-LING CHECK PASSED" .scratch/verify/kindling.log; then
  echo "  $(grep 'internal airs: n=' .scratch/verify/kindling.log | sed 's/^  //')"
  echo "  $(grep 'external airs: n=' .scratch/verify/kindling.log | sed 's/^  //')"
else
  echo "  KINDLING CHECK FAILED"; tail -4 .scratch/verify/kindling.log; fail=1
fi
if python3 scripts/element_holes.py > .scratch/verify/holes.log 2>&1 \
   && grep -q "HOLES CHECK PASSED" .scratch/verify/holes.log; then
  echo "  $(grep 'total pore' .scratch/verify/holes.log | sed 's/^  //')"
  echo "  $(grep 'hole-free elements' .scratch/verify/holes.log | sed 's/^  //')"
else
  echo "  HOLES CHECK FAILED"; tail -4 .scratch/verify/holes.log; fail=1
fi

echo "== The counterflow test"
if python3 scripts/counterflow_test.py > .scratch/verify/counter.log 2>&1 \
   && grep -q "COUNTERFLOW TEST" .scratch/verify/counter.log; then
  echo "  $(grep 'against the pin' .scratch/verify/counter.log | sed 's/^  //')"
  echo "  $(grep 'COUNTERFLOW TEST' .scratch/verify/counter.log | sed 's/^  //')"
  echo "  $(grep 'CORNER TEST' .scratch/verify/counter.log | sed 's/^  //')"
else
  echo "  COUNTERFLOW TEST FAILED"; tail -4 .scratch/verify/counter.log; fail=1
fi

echo "== The digit ratio equation"
if python3 scripts/digit_ratio_equation.py > .scratch/verify/digratio.log 2>&1 \
   && grep -q "DIGIT-RATIO EQUATION PASSED" .scratch/verify/digratio.log; then
  echo "  $(grep 'R_digits = sum' .scratch/verify/digratio.log | sed 's/^  //')"
  echo "  $(grep 'the equation R_digits' .scratch/verify/digratio.log | sed 's/^  //')"
  echo "  $(grep 'DIGIT-RATIO EQUATION PASSED' .scratch/verify/digratio.log | sed 's/^  //')"
else
  echo "  DIGIT-RATIO EQUATION FAILED"; tail -4 .scratch/verify/digratio.log; fail=1
fi

echo "== The un-baking test (3 and 7 one-way, 1 and 9 returnable)"
if python3 scripts/locked_digits.py 1e9 > .scratch/verify/locked.log 2>&1 \
   && grep -q "LOCKED-DIGIT TEST PASSED" .scratch/verify/locked.log; then
  echo "  $(grep 'closer 3:' .scratch/verify/locked.log | sed 's/^ *//')"
  echo "  $(grep 'the plain pin' .scratch/verify/locked.log | sed 's/^  //')"
  echo "  $(grep 'with the digit' .scratch/verify/locked.log | sed 's/^  //')"
  echo "  $(grep 'below the closure 54' .scratch/verify/locked.log | sed 's/^  //')"
else
  echo "  UN-BAKING TEST FAILED"; tail -4 .scratch/verify/locked.log; fail=1
fi

echo "== The scaled formulas for primes (energy, acceleration, mass)"
if python3 scripts/prime_scales.py 1e9 > .scratch/verify/scales.log 2>&1 \
   && grep -q "PRIME SCALES PASSED" .scratch/verify/scales.log; then
  echo "  $(grep 'all handoffs: Ê' .scratch/verify/scales.log | sed 's/^  //')"
  echo "  $(grep 'acceleration a = 2Ê' .scratch/verify/scales.log | sed 's/^  //')"
  echo "  $(grep 'mass m̂' .scratch/verify/scales.log | sed 's/^  //')"
  echo "  $(grep '3R·κ' .scratch/verify/scales.log | sed 's/^  //')"
else
  echo "  PRIME SCALES FAILED"; tail -4 .scratch/verify/scales.log; fail=1
fi

echo "== Do the gap digits drive the fission ratio"
if python3 scripts/gap_digits_fission.py 1e9 > .scratch/verify/gapdig.log 2>&1 \
   && grep -q "GAP-DIGIT TEST PASSED" .scratch/verify/gapdig.log; then
  echo "  $(grep "every air's digit fixes" .scratch/verify/gapdig.log | sed 's/^  //')"
  echo "  $(grep 'hits .* of .*; chance' .scratch/verify/gapdig.log | sed 's/^  //')"
  echo "  $(grep 'largest raw correlation' .scratch/verify/gapdig.log | sed 's/^  //')"
  echo "  $(grep 'share-weighted mean' -A1 .scratch/verify/gapdig.log | tail -1 | sed 's/^  //')"
else
  echo "  GAP-DIGIT TEST FAILED"; tail -4 .scratch/verify/gapdig.log; fail=1
fi

echo "== The per-system digit-ratio test"
if python3 scripts/per_system_digit_ratio.py 1e9 > .scratch/verify/persys.log 2>&1 \
   && grep -q "PER-SYSTEM TEST" .scratch/verify/persys.log; then
  echo "  $(grep 'random windows of' .scratch/verify/persys.log | sed 's/^  //')"
  echo "  $(grep 'spread of R_digits' .scratch/verify/persys.log | sed 's/^  //')"
  echo "  $(grep 'shuffle null' .scratch/verify/persys.log | sed 's/^  //')"
else
  echo "  PER-SYSTEM TEST FAILED"; tail -4 .scratch/verify/persys.log; fail=1
fi

echo "== Atom, nucleus, or smaller"
if python3 scripts/atom_or_nucleus.py > .scratch/verify/nucleus.log 2>&1 \
   && grep -q "ATOM-OR-NUCLEUS TEST PASSED" .scratch/verify/nucleus.log; then
  echo "  $(grep 'Z_H = ' .scratch/verify/nucleus.log | sed 's/^  //')"
  echo "  $(grep 'N_H = ' .scratch/verify/nucleus.log | sed 's/^  //')"
  echo "  $(grep '54 + 82' .scratch/verify/nucleus.log | sed 's/^  //')"
else
  echo "  ATOM-OR-NUCLEUS FAILED"; tail -4 .scratch/verify/nucleus.log; fail=1
fi

echo "== The Light Chart (types, core, ratio)"
if python3 scripts/light_chart.py > .scratch/verify/chart.log 2>&1; then
  echo "  $(grep 'ratio band' .scratch/verify/chart.log | sed 's/^  //')"
  echo "  $(grep 'block pairs' .scratch/verify/chart.log | sed 's/^  //')"
else
  echo "  LIGHT CHART FAILED"; tail -4 .scratch/verify/chart.log; fail=1
fi

echo "== Paper (results/light-bridge-paper.md)"
python3 scripts/paper-inventory.py > /dev/null 2>&1
if python3 scripts/check-paper.py > .scratch/verify/paper.log 2>&1 \
   && grep -q "PAPER CHECKS PASSED" .scratch/verify/paper.log; then
  echo "  $(grep 'names:' .scratch/verify/paper.log | sed 's/^  //'); $(grep -c ' ok$' .scratch/verify/paper.log) quoted numbers agree with the data"
else
  echo "  PAPER CHECKS FAILED"; grep -E "MISSING|MISMATCH" .scratch/verify/paper.log | head -5; fail=1
fi
if command -v pandoc > /dev/null && command -v xelatex > /dev/null; then
  if bash paper/build.sh > .scratch/verify/paperbuild.log 2>&1; then
    echo "  paper/light-bridge-paper.pdf rebuilt ($(pdfinfo paper/light-bridge-paper.pdf 2>/dev/null | awk '/^Pages/{print $2}') pages)"
  else
    echo "  PDF BUILD FAILED"; tail -4 .scratch/verify/paperbuild.log; fail=1
  fi
else
  echo "  (pandoc or xelatex absent: PDF build skipped)"
fi

echo "== Measured numbers (fission theorem)"
if python3 scripts/fission_verify.py | tail -1 | grep -q "0 mismatches"; then
  echo "  $(python3 scripts/fission_verify.py | tail -1)"
else
  echo "  MISMATCH"; python3 scripts/fission_verify.py | grep MISMATCH; fail=1
fi

echo
if [ "$fail" -eq 0 ]; then echo "ALL CHECKS PASSED"; else echo "FAILURES ABOVE"; fi
exit $fail
