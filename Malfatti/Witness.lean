import Malfatti.Main

/-!
# Non-vacuity witnesses

Concrete data showing that the hypotheses of the library's results are jointly satisfiable
(nothing is proved from contradictory assumptions). Each `*_sat` witness also *instantiates* the
lemma it witnesses: its statement is the target lemma's conclusion at concrete arguments, proved by
applying the lemma with its hypotheses discharged inline as the lemma's own arguments (the
hypotheses are not restated separately, so they cannot drift from what the lemma needs). A change
to a target lemma, or to a numeral of a witness, therefore breaks the corresponding application.

* Geometry: the right triangle `(0,0), (1,0), (0,1)` in `EuclideanSpace ℝ (Fin 2)` (`triW`) is a
  genuine triangle, so the headline theorems `malfatti_circles_exist` / `malfatti_circles_formula`
  and every lemma over a triangle in a 2-dimensional space have satisfiable hypotheses.
* Algebra: `r = 1`, `p = q = 1/3`, `w = 1/7` satisfy `0 < p, q, w < 1` and `K p q w = 0`, and
  also Heron's relation in the form used by `K_eq_zero_of_heron` (tangent lengths `4/3, 4/3, 24/7`,
  the isosceles triangle with sides `56, 100, 100` scaled by `1/21`, inradius `1`).
  `r = 3, x = 4, d = 5` satisfies the hypotheses of `param_spec`.
* A non-isosceles, non-unit-inradius algebraic instance: `r = 2`, `p = 1/3, q = 1/5, w = 3/11`
  (`K p q w = 0`), used by `heron_witness_r2` and the algebraic `*_sat` witnesses so that the
  `r`-scaling is exercised.
-/

open EuclideanGeometry Affine AffineMap
open scoped RealInnerProductSpace

namespace Malfatti

/-- The vertices `(0,0), (1,0), (0,1)` are affinely independent. -/
lemma triW_affineIndependent :
    AffineIndependent ℝ ![(!₂[0, 0] : EuclideanSpace ℝ (Fin 2)), !₂[1, 0], !₂[0, 1]] := by
  rw [affineIndependent_iff_not_collinear_set]
  intro h
  rw [collinear_iff_of_mem (p₀ := (!₂[0, 0] : EuclideanSpace ℝ (Fin 2))) (by simp)] at h
  obtain ⟨v, hv⟩ := h
  obtain ⟨r₁, h₁⟩ := hv !₂[1, 0] (by simp)
  obtain ⟨r₂, h₂⟩ := hv !₂[0, 1] (by simp)
  have a0 := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 0) h₁
  have a1 := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 1) h₁
  have b0 := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 0) h₂
  have b1 := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 1) h₂
  simp at a0 a1 b0 b1
  rcases a1 with h | h
  · rw [h] at a0; norm_num at a0
  · rw [h] at b1; norm_num at b1

/-- The concrete right triangle `(0,0), (1,0), (0,1)` in the Euclidean plane. -/
noncomputable def triW : Triangle ℝ (EuclideanSpace ℝ (Fin 2)) :=
  ⟨![!₂[0, 0], !₂[1, 0], !₂[0, 1]], triW_affineIndependent⟩

/-- The Euclidean plane is 2-dimensional. -/
theorem finrank_plane_fact : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) :=
  ⟨finrank_euclideanSpace_fin⟩

/-! ### Headline theorems -/

/-- The hypotheses of `malfatti_circles_exist` (a triangle in the plane) are satisfiable, and the
conclusion of `malfatti_circles_exist` holds for that triangle. -/
theorem malfatti_circles_exist_sat :
    ∃ t : Triangle ℝ (EuclideanSpace ℝ (Fin 2)),
      ∃ c : Fin 3 → Sphere (EuclideanSpace ℝ (Fin 2)),
        (∀ i, 0 < (c i).radius) ∧
        (∀ i j k, i ≠ j → i ≠ k → j ≠ k →
          (c i).IsTangent line[ℝ, t.points i, t.points j] ∧
          line[ℝ, t.points i, t.points j].SSameSide (c i).center (t.points k)) ∧
        (∀ i j, i ≠ j → (c i).IsExtTangent (c j)) :=
  ⟨triW, malfatti_circles_exist triW⟩

/-- The hypotheses of `malfatti_circles_formula` (a triangle in the plane) are satisfiable, and
the conclusion of `malfatti_circles_formula` holds for that triangle. -/
theorem malfatti_circles_formula_sat :
    ∃ t : Triangle ℝ (EuclideanSpace ℝ (Fin 2)),
      ∃ c : Fin 3 → Sphere (EuclideanSpace ℝ (Fin 2)),
        (∀ i, (c i).radius =
          t.inradius / (2 * (semi t - dist (t.points (i + 1)) (t.points (i + 2)))) *
            (semi t - t.inradius - (dist t.incenter (t.points (i + 1)) +
              dist t.incenter (t.points (i + 2)) - dist t.incenter (t.points i)))) ∧
        (∀ i, 0 < (c i).radius) ∧
        (∀ i j k, i ≠ j → i ≠ k → j ≠ k →
          (c i).IsTangent line[ℝ, t.points i, t.points j] ∧
          line[ℝ, t.points i, t.points j].SSameSide (c i).center (t.points k)) ∧
        (∀ i j, i ≠ j → (c i).IsExtTangent (c j)) :=
  ⟨triW, malfatti_circles_formula triW⟩

/-- `malfatti_circles_exist` instantiated at the concrete triangle `triW`. -/
theorem malfatti_circles_exist_triW :
    ∃ c : Fin 3 → Sphere (EuclideanSpace ℝ (Fin 2)),
      (∀ i, 0 < (c i).radius) ∧
      (∀ i j k, i ≠ j → i ≠ k → j ≠ k →
        (c i).IsTangent line[ℝ, triW.points i, triW.points j] ∧
        line[ℝ, triW.points i, triW.points j].SSameSide (c i).center (triW.points k)) ∧
      (∀ i j, i ≠ j → (c i).IsExtTangent (c j)) :=
  malfatti_circles_exist triW

/-- `malfatti_circles_formula` instantiated at the concrete triangle `triW`. -/
theorem malfatti_circles_formula_triW :
    ∃ c : Fin 3 → Sphere (EuclideanSpace ℝ (Fin 2)),
      (∀ i, (c i).radius =
        triW.inradius / (2 * (semi triW - dist (triW.points (i + 1)) (triW.points (i + 2)))) *
          (semi triW - triW.inradius - (dist triW.incenter (triW.points (i + 1)) +
            dist triW.incenter (triW.points (i + 2)) - dist triW.incenter (triW.points i)))) ∧
      (∀ i, 0 < (c i).radius) ∧
      (∀ i j k, i ≠ j → i ≠ k → j ≠ k →
        (c i).IsTangent line[ℝ, triW.points i, triW.points j] ∧
        line[ℝ, triW.points i, triW.points j].SSameSide (c i).center (triW.points k)) ∧
      (∀ i j, i ≠ j → (c i).IsExtTangent (c j)) :=
  malfatti_circles_formula triW

/-! ### Geometric lemmas over a general triangle -/

/-- Hypotheses of `malfattiCircle_radius`, `malfattiCircle_center`, `dist_touch_incenter`,
`touch_mem` (a triangle, three distinct indices) are satisfiable: the statement is the conjunction
of their conclusions at `triW` with indices `0, 1, 2`, each proved by applying the lemma, with the
distinctness hypotheses of `touch_mem` discharged inline. -/
theorem geom_sat :
    (malfattiCircle triW 0).radius = triW.inradius * ratio triW 0 ∧
      (malfattiCircle triW 0).center = lineMap (triW.points 0) triW.incenter (ratio triW 0) ∧
      dist (triW.touchpoint ∅ 2) triW.incenter = triW.inradius ∧
      Sbtw ℝ (triW.points 0) (triW.touchpoint ∅ 2) (triW.points 1) :=
  ⟨malfattiCircle_radius triW 0, malfattiCircle_center triW 0, dist_touch_incenter triW 2,
    touch_mem triW (by decide) (by decide) (by decide)⟩

/-- Hypotheses of every lemma over a triangle in a 2-dimensional space (`perp`, `dist_sq_split`,
`tl_pos`, `tl_eq_dist`, `dist_vertex_sq`, `side_eq`, `gram`, `heron`, `tparam_spec`, `K_zero`,
`K_cyc`, `ratio_pos`, `ratio_lt_one`, `isTangentAt_side`, `sSameSide_center`,
`malfattiCircle_tangent_side`, `center_vsub_incenter`, `isExtTangent_succ`,
`malfattiCircle_radius_pos`, `malfattiCircle_isExtTangent`, `malfattiCircle_radius_lt_inradius`,
`malfattiCircle_radius_formula`) are jointly satisfiable: the statement is the conjunction of the lemmas' conclusions at the
triangle `triW` in the plane, the indices `0, 1, 2`, the point `y = A₀` on line `A₀A₁` and `μ = 1`,
and each conjunct is the target lemma applied to that data, its hypotheses discharged inline. -/
theorem geom_plane_sat :
    -- perp
    ⟪triW.points 0 -ᵥ triW.touchpoint ∅ 2, triW.touchpoint ∅ 2 -ᵥ triW.incenter⟫ = 0 ∧
    -- dist_sq_split
    dist (triW.points 0) triW.incenter ^ 2 =
      dist (triW.points 0) (triW.touchpoint ∅ 2) ^ 2 + triW.inradius ^ 2 ∧
    -- tl_pos
    0 < tl triW 0 ∧
    -- tl_eq_dist
    dist (triW.points 0) (triW.touchpoint ∅ 2) = tl triW 0 ∧
    -- dist_vertex_sq
    dist (triW.points 0) triW.incenter ^ 2 = tl triW 0 ^ 2 + triW.inradius ^ 2 ∧
    -- side_eq
    dist (triW.points 0) (triW.points 1) = tl triW 0 + tl triW 1 ∧
    -- gram
    ⟪triW.points 0 -ᵥ triW.incenter, triW.points 1 -ᵥ triW.incenter⟫ =
      triW.inradius ^ 2 - tl triW 0 * tl triW 1 ∧
    -- heron
    triW.inradius ^ 2 * (tl triW 0 + tl triW 1 + tl triW 2) = tl triW 0 * tl triW 1 * tl triW 2 ∧
    -- tparam_spec
    (0 < tparam triW 0 ∧ tparam triW 0 < 1 ∧ tl triW 0 = X triW.inradius (tparam triW 0) ∧
      dist (triW.points 0) triW.incenter = D triW.inradius (tparam triW 0)) ∧
    -- K_zero
    K (tparam triW 0) (tparam triW 1) (tparam triW 2) = 0 ∧
    -- K_cyc
    K (tparam triW 1) (tparam triW (1 + 1)) (tparam triW (1 + 2)) = 0 ∧
    -- ratio_pos, ratio_lt_one
    0 < ratio triW 0 ∧ ratio triW 0 < 1 ∧
    -- isTangentAt_side
    (⟨lineMap (triW.points 0) triW.incenter (1 : ℝ), triW.inradius * 1⟩ :
        Sphere (EuclideanSpace ℝ (Fin 2))).IsTangentAt
      (lineMap (triW.points 0) (triW.touchpoint ∅ 2) (1 : ℝ)) line[ℝ, triW.points 0, triW.points 1] ∧
    -- sSameSide_center
    line[ℝ, triW.points 0, triW.points 1].SSameSide
      (lineMap (triW.points 0) triW.incenter (1 : ℝ)) (triW.points 2) ∧
    -- malfattiCircle_tangent_side
    ((malfattiCircle triW 0).IsTangentAt
        (lineMap (triW.points 0) (triW.touchpoint ∅ 2) (ratio triW 0))
        line[ℝ, triW.points 0, triW.points 1] ∧
      line[ℝ, triW.points 0, triW.points 1].SSameSide (malfattiCircle triW 0).center
        (triW.points 2)) ∧
    -- center_vsub_incenter
    (malfattiCircle triW 0).center -ᵥ triW.incenter =
      (1 - ratio triW 0) • (triW.points 0 -ᵥ triW.incenter) ∧
    -- isExtTangent_succ
    (malfattiCircle triW 0).IsExtTangent (malfattiCircle triW (0 + 1)) ∧
    -- malfattiCircle_radius_pos
    0 < (malfattiCircle triW 0).radius ∧
    -- malfattiCircle_isExtTangent
    (malfattiCircle triW 0).IsExtTangent (malfattiCircle triW 2) ∧
    -- malfattiCircle_radius_lt_inradius
    (malfattiCircle triW 0).radius < triW.inradius ∧
    -- malfattiCircle_radius_formula
    (malfattiCircle triW 0).radius =
      triW.inradius / (2 * (semi triW - dist (triW.points (0 + 1)) (triW.points (0 + 2)))) *
        (semi triW - triW.inradius - (dist triW.incenter (triW.points (0 + 1)) +
          dist triW.incenter (triW.points (0 + 2)) - dist triW.incenter (triW.points 0))) := by
  have := finrank_plane_fact
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  exact ⟨perp triW h01 h02 h12 (left_mem_affineSpan_pair ℝ _ _), dist_sq_split triW h01 h02 h12, tl_pos triW 0,
    tl_eq_dist triW h01 h02 h12, dist_vertex_sq triW 0, side_eq triW h01 h02 h12,
    gram triW h01, heron triW, tparam_spec triW 0, K_zero triW, K_cyc triW 1,
    ratio_pos triW 0, ratio_lt_one triW 0, isTangentAt_side triW h01 h02 h12 zero_le_one,
    sSameSide_center triW h01 h02 h12 one_pos, malfattiCircle_tangent_side triW h01 h02 h12,
    center_vsub_incenter triW 0, isExtTangent_succ triW 0, malfattiCircle_radius_pos triW 0,
    malfattiCircle_isExtTangent triW h02, malfattiCircle_radius_lt_inradius triW 0,
    malfattiCircle_radius_formula triW 0⟩

/-! ### Algebraic lemmas

Each witness below is the conclusion of its target lemma at concrete arguments; the lemma's
hypotheses are discharged inline as the lemma's own arguments (their types are fixed by the lemma,
not restated), and Heron's relation / the tangent relation are passed as the named witnesses
`heron_witness`, `heron_witness_r2`, `K_eq_zero_of_heron_sat`. Changing any numeral therefore
makes an application fail rather than produce a different true statement. -/

/-- Heron's relation for `r = 1` and parameters `1/3, 1/3, 1/7` (tangent lengths
`4/3, 4/3, 24/7`). It is the Heron hypothesis fed to `K_eq_zero_of_heron` in `K_witness`. -/
theorem heron_witness :
    (1 : ℝ) ^ 2 * (X 1 (1 / 3) + X 1 (1 / 3) + X 1 (1 / 7)) =
      X 1 (1 / 3) * X 1 (1 / 3) * X 1 (1 / 7) := by
  norm_num [X]

/-- Heron's relation for `r = 2` (so the `r`-scaling is exercised) and parameters
`1/3, 1/5, 3/11` (tangent lengths `8/3, 24/5, 56/33`). It is the Heron hypothesis fed to
`K_eq_zero_of_heron` in `K_eq_zero_of_heron_sat`. -/
theorem heron_witness_r2 :
    (2 : ℝ) ^ 2 * (X 2 (1 / 3) + X 2 (1 / 5) + X 2 (3 / 11)) =
      X 2 (1 / 3) * X 2 (1 / 5) * X 2 (3 / 11) := by
  norm_num [X]

/-- The tangent relation `K p q w = 0` has a solution with `p, q, w ∈ (0, 1)`: `p = q = 1/3,
w = 1/7`, obtained from `K_eq_zero_of_heron` at `r = 1` with the bounds `0 < · < 1` discharged
inline and Heron's relation supplied by `heron_witness`. -/
theorem K_witness : K (1 / 3) (1 / 3) (1 / 7) = 0 :=
  K_eq_zero_of_heron (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) heron_witness

/-- Hypotheses of `K_eq_zero_of_heron` are satisfiable (`r = 2`, `p, q, w = 1/3, 1/5, 3/11`): its
conclusion at that data, with the bounds discharged inline and Heron's relation supplied by
`heron_witness_r2`. -/
theorem K_eq_zero_of_heron_sat : K (1 / 3) (1 / 5) (3 / 11) = 0 :=
  K_eq_zero_of_heron (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) heron_witness_r2

/-- A second, non-isosceles solution of the tangent relation, `(1/5, 3/11, 1/3)`: the cyclic
permutation (`K_perm₁`) of the solution produced by `K_eq_zero_of_heron_sat`. -/
theorem K_witness_scalene : K (1 / 5) (3 / 11) (1 / 3) = 0 :=
  (K_perm₁ _ _ _).symm.trans K_eq_zero_of_heron_sat

/-- Hypotheses of `radius_eq` are satisfiable (`r = 2`, `p, q, w = 1/3, 1/5, 3/11`): its
conclusion at that data, with the bounds discharged inline and `K = 0` supplied by
`K_eq_zero_of_heron_sat`. -/
theorem radius_eq_sat :
    2 / (2 * X 2 (1 / 3)) * ((X 2 (1 / 3) + X 2 (1 / 5) + X 2 (3 / 11)) - 2 -
        (D 2 (1 / 5) + D 2 (3 / 11) - D 2 (1 / 3))) = 2 * mu (1 / 3) (1 / 5) (3 / 11) :=
  radius_eq (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    K_eq_zero_of_heron_sat

/-- Hypotheses of `dist_identity` are satisfiable (`r = 2`, `p, q, w = 1/3, 1/5, 3/11`): its
conclusion at that data, with the bounds discharged inline and `K = 0` supplied by
`K_eq_zero_of_heron_sat`. -/
theorem dist_identity_sat :
    (1 - mu (1 / 3) (1 / 5) (3 / 11)) ^ 2 * (X 2 (1 / 3) ^ 2 + 2 ^ 2) +
        (1 - mu (1 / 5) (3 / 11) (1 / 3)) ^ 2 * (X 2 (1 / 5) ^ 2 + 2 ^ 2) -
        2 * (1 - mu (1 / 3) (1 / 5) (3 / 11)) * (1 - mu (1 / 5) (3 / 11) (1 / 3)) *
          (2 ^ 2 - X 2 (1 / 3) * X 2 (1 / 5)) =
      (2 * mu (1 / 3) (1 / 5) (3 / 11) + 2 * mu (1 / 5) (3 / 11) (1 / 3)) ^ 2 :=
  dist_identity (by norm_num) (by norm_num) (by norm_num) K_eq_zero_of_heron_sat

/-- Hypotheses of `mu_lt_one` are satisfiable (`p, q, w = 1/3, 1/5, 3/11`): its conclusion at that
data, with the bounds discharged inline and `K = 0` supplied by `K_eq_zero_of_heron_sat`. -/
theorem mu_lt_one_sat : mu (1 / 3) (1 / 5) (3 / 11) < 1 :=
  mu_lt_one (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    K_eq_zero_of_heron_sat

/-- Hypotheses of `param_spec` are satisfiable (`r = 3, x = 4, d = 5`): its conclusion at that
data, with the hypotheses (positivity and `5² = 4² + 3²`) discharged inline. -/
theorem param_spec_sat :
    0 < ((5 : ℝ) - 4) / 3 ∧ ((5 : ℝ) - 4) / 3 < 1 ∧ (4 : ℝ) = X 3 ((5 - 4) / 3) ∧
      (5 : ℝ) = D 3 ((5 - 4) / 3) :=
  param_spec (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end Malfatti
