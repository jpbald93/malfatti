#!/bin/bash
# Gate for the Lean formalisation. It passes only if all of these hold:
#  * the sources contain no `sorry`, `admit`, `native_decide`, `axiom` keyword (anywhere,
#    including one on a line of its own), `#eval`, `run_cmd`, `initialize`, `IO`, `set_option`,
#    or syntax-extension commands (`macro`, `elab`, `syntax`, `notation`, `import Lean`, ...),
#    which could redefine `#print axioms`;
#  * the library builds without errors;
#  * the gate itself (not a file in the repo) generates the `#print axioms` report for each
#    REQUIRED theorem, and each report is present exactly once;
#  * each REQUIRED theorem (with its transitive dependencies) uses only Lean's standard axioms
#    (propext, Classical.choice, Quot.sound).
# Trust boundary: the token filter is a heuristic over the project's .lean sources. The gate assumes
# the pinned toolchain, Mathlib and lake configuration are unmodified. It is not a sandbox, and it
# does not audit declarations other than the REQUIRED theorems.
# REQUIRED lists, fully qualified, every declaration of this library cited in SPIKE_REPORT.md
# plus every name queried by scratch/Ax.lean; definitions may use a subset of the standard axioms.
# Lean wraps long axiom lists across several lines, so the output is flattened before parsing.
export PATH="$HOME/.elan/bin:$PATH"
cd "$(dirname "$0")" || exit 1
NS="Malfatti"
LIB="Malfatti"
REQUIRED="Malfatti.D Malfatti.K Malfatti.K_cyc Malfatti.K_eq_zero_of_heron Malfatti.K_perm₁ Malfatti.K_zero Malfatti.X Malfatti.center_vsub_incenter Malfatti.dist_identity Malfatti.dist_sq_split Malfatti.dist_touch_incenter Malfatti.dist_vertex_sq Malfatti.fin3_add Malfatti.fin3_distinct Malfatti.fin3_third Malfatti.gram Malfatti.heron Malfatti.isExtTangent_succ Malfatti.isTangentAt_side Malfatti.lineMap_vsub_lineMap_same Malfatti.malfattiCircle Malfatti.malfattiCircle_center Malfatti.malfattiCircle_isExtTangent Malfatti.malfattiCircle_radius Malfatti.malfattiCircle_radius_formula Malfatti.malfattiCircle_radius_lt_inradius Malfatti.malfattiCircle_radius_pos Malfatti.malfattiCircle_tangent_side Malfatti.malfatti_circles_exist Malfatti.malfatti_circles_formula Malfatti.mu Malfatti.mu_comm Malfatti.mu_lt_one Malfatti.mu_pos Malfatti.param_spec Malfatti.perp Malfatti.radius_eq Malfatti.ratio Malfatti.ratio_lt_one Malfatti.ratio_pos Malfatti.sSameSide_center Malfatti.semi Malfatti.side_eq Malfatti.sum_cyc Malfatti.tl Malfatti.tl_eq_dist Malfatti.tl_pos Malfatti.touch_mem Malfatti.tparam Malfatti.tparam_spec Malfatti.D_bridge Malfatti.K_bridge Malfatti.X_bridge Malfatti.malfattiCircle_bridge Malfatti.mu_bridge Malfatti.ratio_bridge Malfatti.semi_bridge Malfatti.tl_bridge Malfatti.tparam_bridge Malfatti.triW_affineIndependent Malfatti.triW Malfatti.finrank_plane_fact Malfatti.malfatti_circles_exist_sat Malfatti.malfatti_circles_formula_sat Malfatti.malfatti_circles_exist_triW Malfatti.malfatti_circles_formula_triW Malfatti.geom_sat Malfatti.geom_plane_sat Malfatti.K_witness Malfatti.K_witness_scalene Malfatti.heron_witness Malfatti.heron_witness_r2 Malfatti.K_eq_zero_of_heron_sat Malfatti.radius_eq_sat Malfatti.dist_identity_sat Malfatti.mu_lt_one_sat Malfatti.param_spec_sat"
SOURCES="Malfatti/*.lean Malfatti.lean"
# Never fetch: the pinned Mathlib checkout must already be present.
[ -e .lake/packages/mathlib ] || { echo "FAIL: Mathlib packages missing (run setup by hand)"; exit 1; }
if grep -nE "\bsorry\b|\badmit\b|native_decide|\baxiom\b|#eval|\brun_cmd\b|\binitialize\b|\bIO\b|\bdebug\.|\bmacro|\belab|\bsyntax\b|\bnotation\b|\binfix|\bprefix\b|\bpostfix\b|import Lean|open Lean|\bset_option\b" $SOURCES; then
  echo "FAIL: forbidden token"; exit 1; fi
build=$(lake build $LIB 2>&1); bstatus=$?
printf '%s\n' "$build" | tail -3
[ "$bstatus" -eq 0 ] || { printf '%s\n' "$build"; echo "FAIL: build"; exit 1; }
root=$(lake env lean "$LIB.lean" 2>&1) || { printf '%s\n' "$root"; echo "FAIL: build (root file)"; exit 1; }
# The `#print axioms` queries are generated here rather than read from a file in the repo.
# Portable (no GNU mktemp); the leading dot keeps it out of the SOURCES glob.
chk=".gatecheck_$$.lean"
trap 'rm -f "$chk"' EXIT
{ echo "import $LIB"; for t in $REQUIRED; do echo "#print axioms $t"; done; } > "$chk"
out=$(lake env lean "$chk" 2>&1); status=$?
printf '%s\n' "$out"
[ "$status" -eq 0 ] || { echo "FAIL: axiom report"; exit 1; }
echo "$out" | grep -qE "(^|:)[[:space:]]*error" && { echo "FAIL: Lean reported an error"; exit 1; }
flat=$(printf '%s\n' "$out" | awk '/^'"'"'/{if(buf!="")print buf; buf=$0; next} {buf=buf" "$0} END{if(buf!="")print buf}')
reports=$(printf '%s\n' "$flat" | grep -E "depends on axioms|does not depend on any axioms")
n=0
for t in $REQUIRED; do
  te=$(printf '%s' "$t" | sed 's/[.]/\\./g')
  c=$(printf '%s\n' "$reports" | grep -cE "^'$te' (depends on axioms|does not depend)")
  [ "$c" -eq 1 ] || { echo "FAIL: expected one axiom report for $t, found $c"; exit 1; }
  n=$((n+1))
done
[ "$(printf '%s\n' "$reports" | grep -c .)" -eq "$n" ] || { echo "FAIL: unexpected extra reports"; exit 1; }
printf '%s\n' "$reports" | grep "depends on axioms" | grep -qv '\]' && { echo "FAIL: unterminated axiom list"; exit 1; }
bad=$(printf '%s\n' "$reports" | grep "depends on axioms" | sed 's/.*depends on axioms: *\[//; s/\].*//' \
      | tr ',' '\n' | sed 's/^ *//; s/ *$//' | grep -v '^$' | sort -u \
      | grep -vE '^(propext|Classical\.choice|Quot\.sound)$')
[ -n "$bad" ] && { echo "FAIL: nonstandard axioms: $bad"; exit 1; }
echo "PASS ($n declarations, standard axioms only)"
