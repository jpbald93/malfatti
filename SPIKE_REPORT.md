# malfatti — Malfatti circles (existence + Malfatti's radius formula)

**Status: DONE** for target (1). Target (2), the Malfatti *problem* (greedy optimality, Zalgaller–Los' 1994), was not attempted, as instructed. The Lob–Richmond counterexample is checked numerically only (Python).

## Step 0: prior art
- Mathlib v4.33.1: there is no Malfatti material (`grep -rn alfatti Mathlib docs` finds nothing). There is no entry in 100.yaml or 1000.yaml. Infrastructure that is there: `Affine.Simplex.incenter/inradius/touchpoint`, `Sphere.IsTangentAt`, `Sphere.IsExtTangent` and `Triangle.sbtw_touchpoint_empty`.
- `gh search code "Malfatti" language:lean`: no hits. `gh search repos malfatti`: only unrelated repos named after people called Malfatti. `gh search prs --repo leanprover-community/mathlib4 malfatti`: none.
- I searched the web for Isabelle AFP, HOL Light, Coq/Rocq and Mizar formalisations and found none.

## Headline theorems (all axioms: propext, Classical.choice, Quot.sound)
`Malfatti/Main.lean:15`
```lean
theorem malfatti_circles_exist (t : Triangle ℝ (EuclideanSpace ℝ (Fin 2))) :
    ∃ c : Fin 3 → Sphere (EuclideanSpace ℝ (Fin 2)),
      (∀ i, 0 < (c i).radius) ∧
      (∀ i j k, i ≠ j → i ≠ k → j ≠ k →
        (c i).IsTangent line[ℝ, t.points i, t.points j] ∧
        line[ℝ, t.points i, t.points j].SSameSide (c i).center (t.points k)) ∧
      (∀ i j, i ≠ j → (c i).IsExtTangent (c j))
```
`Malfatti/Main.lean:31`, `malfatti_circles_formula`: the same statement, plus for every `i`
```lean
(c i).radius = t.inradius / (2 * (semi t - dist (t.points (i + 1)) (t.points (i + 2)))) *
  (semi t - t.inradius - (dist t.incenter (t.points (i + 1)) +
    dist t.incenter (t.points (i + 2)) - dist t.incenter (t.points i)))
```
This is `ρ_A = r/(2(s−a))·(s − r − (IB + IC − IA))`, where `semi t` = (sum of the three side lengths)/2.

What the hypotheses and conclusions mean:
- `Triangle` is Mathlib's affinely independent triple, so the triangle is nondegenerate.
- Circle `i` is tangent (Mathlib `IsTangent`) to both side lines through vertex `i`.
- Its centre lies strictly on the same side of each of those lines as the third vertex, i.e. on the interior side.
- Any two of the circles are externally tangent (Mathlib `IsExtTangent`: the distance between centres is the sum of the radii, and both radii are ≥ 0).

General-space versions, for any `Triangle ℝ P` with `Fact (finrank ℝ V = 2)`, are in `Malfatti/Geometry.lean`:
- `malfattiCircle_tangent_side` (line 240) also gives the explicit tangency point. It is `lineMap A_i T μ`, where T is the incircle touch point and μ ∈ (0,1), so it lies on the side segment.
- `malfattiCircle_isExtTangent` (line 280).
- `malfattiCircle_radius_formula` (line 298).
- `malfattiCircle_radius_lt_inradius`.

## Construction and proof
- **Construction.** Each centre is on the segment from vertex `A_i` to the incenter: `O_i = A_i + μ_i (I − A_i)`, with radius `μ_i r`.
- **The ratio μ.** `μ_A = (1+q)(1+w)/(2(1+p))`, where `p = (IA − (s−a))/r` (which equals tan(A/4)).
- **Side tangency** follows by homothety from the incircle tangency (`perp`, `isTangentAt_side`).
- **The angle relation.**
  - Heron's relation `r²s = (s−a)(s−b)(s−c)` (`heron`) is proved from the barycentric description of the incenter, `Σ wᵢ (Aᵢ − I) = 0`, together with the Gram matrix `⟨Aᵢ−I, Aⱼ−I⟩ = r² − xᵢxⱼ`, using an explicit `linear_combination` certificate.
  - Heron's relation gives `K(p,q,w) = 0`, the tangent form of A/4+B/4+C/4 = π/4 (`K_eq_zero_of_heron`). The sign of the cofactor is controlled because 0 < p, q, w < 1.
- **Pairwise tangency and the radius formula** are polynomial identities that are multiples of K (`dist_identity`, `radius_eq`). The certificates were found with sympy (`code/cert.py`, `code/cert2.py`).

## Numerics (`code/check_malfatti.py`, output in `code/check.out`)
- **Formula check.** Over 2000 random triangles, the formula radii with centres on the bisectors have maximum tangency error 2.6e-10.
- **Negative control.** Perturbing the formula by +0.01 inside the bracket gives errors of at least 6.5e-3.
- **Lob–Richmond counterexample.** For the equilateral triangle with side 1:
  - the three Malfatti circles have total area 0.315670;
  - the incircle plus two corner circles of radius r/3 have total area 0.319977, which is larger.

## Gate (seen)
- After `rm -rf .lake/build`, a full `lake build` gives: `Build completed successfully (8710 jobs).`, `EXIT 0`, 0 warnings, 0 errors.
- The forbidden-token grep over `Malfatti Malfatti.lean` finds nothing (grep exit code 1).
- `scratch/ax.out`: all six theorems printed (`malfatti_circles_exist`, `malfatti_circles_formula`, `malfattiCircle_tangent_side`, `malfattiCircle_isExtTangent`, `malfattiCircle_radius_formula`, `heron`) depend only on [propext, Classical.choice, Quot.sound].

## Not done
- **Uniqueness of the Malfatti circles: not proved.** Only existence is proved, by verifying the explicit construction.
- **Containment: only partly proved.** I did not prove that each circle lies inside the triangle. What is proved is that the tangency points lie on the side segments and that the centres lie in the interior half-planes.
- **Malfatti's area problem (Lob–Richmond, Zalgaller–Los'): not attempted.** It is out of scope; the counterexample is checked numerically only.
