import Malfatti.Main

/-!
# Definition bridges

One lemma per local definition of the library, tying it to the standard notion it is meant to
denote.  Nothing here is used by the other modules; this file only adds declarations.

* `X_bridge`      : `X r (tan θ) = r / tan (2θ)`, i.e. `r · cot (A/2)` for `θ = A/4`.
* `D_bridge`      : `D r (tan θ) = r / sin (2θ)`, i.e. `r / sin (A/2)` for `θ = A/4`.
* `K_bridge`      : `K (tan a) (tan b) (tan c) = 0 ↔ a + b + c = π/4` for `a, b, c ∈ (0, π/4)`.
* `mu_bridge`     : `r · mu (tan (A/4)) (tan (B/4)) (tan (C/4))` (Mathlib angles) equals
                    Malfatti's classical radius `r / (2 (s - a)) · (s - r - (IB + IC - IA))`.
* `tl_bridge`     : `tl t i = s - a_i`, and it is the distance from the vertex to the touchpoint.
* `tparam_bridge` : `tparam t i = tan (∠ A_{i+1} A_i A_{i+2} / 4)` (Mathlib unoriented angle).
* `ratio_bridge`  : `ratio t i = ρ_i / r`, and it is the vertex-to-centre over vertex-to-incenter
                    distance ratio along the bisector.
* `malfattiCircle_bridge` : the circle has the defining properties of a Malfatti circle.
* `semi_bridge`   : `semi t` is half the perimeter `∑ |A_i A_{i+1}|` and equals `∑ tl t i`.
-/

open EuclideanGeometry Affine AffineMap
open Real

namespace Malfatti

/-! ### Algebraic definitions -/

/-- Bridge for `X`: with `t = tan θ` (`θ = A/4`), `X r t = r / tan (2θ) = r · cot (A/2)`, the
classical tangent length `s - a`. -/
theorem X_bridge (r θ : ℝ) : X r (tan θ) = r / tan (2 * θ) := by
  rw [tan_two_mul, div_div_eq_mul_div]
  unfold X
  ring

/-- Bridge for `D`: with `t = tan θ` (`θ = A/4 ∈ (0, π/2)`), `D r t = r / sin (2θ) = r / sin (A/2)`,
the classical distance from a vertex to the incenter. -/
theorem D_bridge (r : ℝ) {θ : ℝ} (h0 : 0 < θ) (h1 : θ < π / 2) :
    D r (tan θ) = r / sin (2 * θ) := by
  have hs : 0 < sin θ := sin_pos_of_pos_of_lt_pi h0 (by linarith [pi_pos])
  have hc : 0 < cos θ := cos_pos_of_mem_Ioo ⟨by linarith, h1⟩
  have hsc := sin_sq_add_cos_sq θ
  unfold D
  rw [tan_eq_sin_div_cos, sin_two_mul]
  field_simp
  linear_combination r * hsc

/-- Bridge for `K`: for `a, b, c ∈ (0, π/4)`, `K (tan a) (tan b) (tan c) = 0` is exactly the angle
relation `a + b + c = π/4` (that is, `A/4 + B/4 + C/4 = π/4`). -/
theorem K_bridge {a b c : ℝ} (ha0 : 0 < a) (ha1 : a < π / 4) (hb0 : 0 < b) (hb1 : b < π / 4)
    (hc0 : 0 < c) (hc1 : c < π / 4) :
    K (tan a) (tan b) (tan c) = 0 ↔ a + b + c = π / 4 := by
  have hpi := pi_pos
  have ca : 0 < cos a := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have cb : 0 < cos b := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have cc : 0 < cos c := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have key : K (tan a) (tan b) (tan c) * (cos a * cos b * cos c) =
      cos (a + b + c) - sin (a + b + c) := by
    simp only [cos_add, sin_add, tan_eq_sin_div_cos]
    unfold K
    field_simp
    ring
  have hprod : cos a * cos b * cos c ≠ 0 := by positivity
  have hshift : cos (a + b + c + π / 4) = (cos (a + b + c) - sin (a + b + c)) * (√2 / 2) := by
    rw [cos_add, cos_pi_div_four, sin_pi_div_four]; ring
  constructor
  · intro hK
    have h0 : cos (a + b + c + π / 4) = cos (π / 2) := by
      rw [cos_pi_div_two, hshift, ← key, hK]; ring
    have := injOn_cos ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ h0
    linarith
  · intro h
    have h0 : cos (a + b + c) - sin (a + b + c) = 0 := by
      rw [h, cos_pi_div_four, sin_pi_div_four, sub_self]
    rw [← key] at h0
    exact (mul_eq_zero.1 h0).resolve_right hprod

/-! ### Geometric definitions -/

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [Fact (Module.finrank ℝ V = 2)]

/-- Bridge for `semi`: it is half the perimeter `∑ |A_i A_{i+1}|`, and equals the sum of the three
tangent lengths. -/
theorem semi_bridge (t : Triangle ℝ P) :
    2 * semi t = ∑ i : Fin 3, dist (t.points i) (t.points (i + 1)) ∧
      semi t = ∑ i : Fin 3, tl t i := by
  constructor
  · rw [Fin.sum_univ_three, show (0 : Fin 3) + 1 = 1 by decide, show (1 : Fin 3) + 1 = 2 by decide,
      show (2 : Fin 3) + 1 = 0 by decide]
    unfold semi
    ring
  · rw [Fin.sum_univ_three]
    unfold semi
    rw [side_eq t (by decide : (0 : Fin 3) ≠ 1) (by decide : (0 : Fin 3) ≠ 2)
        (by decide : (1 : Fin 3) ≠ 2),
      side_eq t (by decide : (1 : Fin 3) ≠ 2) (by decide : (1 : Fin 3) ≠ 0)
        (by decide : (2 : Fin 3) ≠ 0),
      side_eq t (by decide : (2 : Fin 3) ≠ 0) (by decide : (2 : Fin 3) ≠ 1)
        (by decide : (0 : Fin 3) ≠ 1)]
    ring

/-- Bridge for `tl`: the tangent length from vertex `i` is `s - a_i`, and it is the distance from
the vertex to the incircle's touchpoint on an adjacent side. -/
theorem tl_bridge (t : Triangle ℝ P) (i : Fin 3) :
    tl t i = semi t - dist (t.points (i + 1)) (t.points (i + 2)) ∧
      tl t i = dist (t.points i) (t.touchpoint ∅ (i + 2)) := by
  obtain ⟨hd1, hd2, hd3⟩ := fin3_distinct i
  refine ⟨?_, (tl_eq_dist t hd1 hd2 hd3).symm⟩
  rw [(semi_bridge t).2, Fin.sum_univ_three, ← sum_cyc (tl t) i, side_eq t hd3 hd1.symm hd2.symm]
  ring

/-- Bridge for `tparam`: the metrically defined parameter is `tan (A_i / 4)`, where `A_i` is the
(Mathlib, unoriented) angle of the triangle at vertex `i`. -/
theorem tparam_bridge (t : Triangle ℝ P) (i : Fin 3) :
    tparam t i = tan (∠ (t.points (i + 1)) (t.points i) (t.points (i + 2)) / 4) := by
  obtain ⟨hd1, hd2, hd3⟩ := fin3_distinct i
  obtain ⟨p0, p1, px, -⟩ := tparam_spec t i
  have hr := t.inradius_pos
  have hx := tl_pos t i
  have hy := tl_pos t (i + 1)
  have hz := tl_pos t (i + 2)
  have hH : t.inradius ^ 2 * (tl t i + tl t (i + 1) + tl t (i + 2)) -
      tl t i * tl t (i + 1) * tl t (i + 2) = 0 := by
    have h := heron t
    have hs := sum_cyc (tl t) i
    have hp : tl t i * tl t (i + 1) * tl t (i + 2) = tl t 0 * tl t 1 * tl t 2 := by
      rcases (by decide : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2) i with rfl | rfl | rfl
      · rw [show (0 : Fin 3) + 1 = 1 by decide, show (0 : Fin 3) + 2 = 2 by decide]
      · rw [show (1 : Fin 3) + 1 = 2 by decide, show (1 : Fin 3) + 2 = 0 by decide]; ring
      · rw [show (2 : Fin 3) + 1 = 0 by decide, show (2 : Fin 3) + 2 = 1 by decide]; ring
    rw [hs, hp, h, sub_self]
  have hL := law_cos (t.points (i + 1)) (t.points i) (t.points (i + 2))
  rw [side_eq t hd3 hd1.symm hd2.symm, side_eq t hd1.symm hd3 hd2,
    side_eq t hd2.symm hd3.symm hd1] at hL
  set A := ∠ (t.points (i + 1)) (t.points i) (t.points (i + 2)) with hAdef
  have hcos : (cos A * (tl t i ^ 2 + t.inradius ^ 2) - (tl t i ^ 2 - t.inradius ^ 2)) *
      ((tl t i + tl t (i + 1)) * (tl t i + tl t (i + 2))) = 0 := by
    linear_combination ((tl t i ^ 2 + t.inradius ^ 2) / 2) * hL + 2 * tl t i * hH
  have hcos' : cos A = (tl t i ^ 2 - t.inradius ^ 2) / (tl t i ^ 2 + t.inradius ^ 2) := by
    rw [eq_div_iff (by positivity)]
    have := (mul_eq_zero.1 hcos).resolve_right (by positivity)
    linarith
  set p := tparam t i with hpdef
  have hθ0 : 0 < arctan p := arctan_pos.2 p0
  have hθ1 : arctan p < π / 4 := by rw [← arctan_one]; exact arctan_lt_arctan_iff.2 p1
  have hc4 : cos (4 * arctan p) = 2 * (2 * (1 / (1 + p ^ 2)) - 1) ^ 2 - 1 := by
    rw [show 4 * arctan p = 2 * (2 * arctan p) by ring, cos_two_mul, cos_two_mul, cos_sq_arctan]
  have hE : (tl t i ^ 2 - t.inradius ^ 2) / (tl t i ^ 2 + t.inradius ^ 2) =
      2 * (2 * (1 / (1 + p ^ 2)) - 1) ^ 2 - 1 := by
    rw [px]
    unfold X
    field_simp
    ring
  have hAeq : A = 4 * arctan p :=
    injOn_cos ⟨angle_nonneg _ _ _, angle_le_pi _ _ _⟩
      ⟨by linarith, by linarith [pi_pos]⟩ (by rw [hcos', hE, hc4])
  rw [hAeq, show 4 * arctan p / 4 = arctan p by ring, tan_arctan]

/-- Bridge for `mu`: evaluated at the tangents of the quarter angles (Mathlib angles) of a plane
triangle, `r · mu` is Malfatti's classical radius `r / (2 (s - a)) · (s - r - (IB + IC - IA))`. -/
theorem mu_bridge (t : Triangle ℝ P) (i : Fin 3) :
    t.inradius * mu (tan (∠ (t.points (i + 1)) (t.points i) (t.points (i + 2)) / 4))
        (tan (∠ (t.points (i + 2)) (t.points (i + 1)) (t.points i) / 4))
        (tan (∠ (t.points i) (t.points (i + 2)) (t.points (i + 1)) / 4)) =
      t.inradius / (2 * (semi t - dist (t.points (i + 1)) (t.points (i + 2)))) *
        (semi t - t.inradius - (dist t.incenter (t.points (i + 1)) +
          dist t.incenter (t.points (i + 2)) - dist t.incenter (t.points i))) := by
  obtain ⟨ha1, ha2⟩ := fin3_add i
  have hb : i + 2 + 1 = i ∧ i + 2 + 2 = i + 1 := by revert i; decide
  have h1 := tparam_bridge t (i + 1)
  have h2 := tparam_bridge t (i + 2)
  rw [ha1, ha2] at h1
  rw [hb.1, hb.2] at h2
  rw [← tparam_bridge t i, ← h1, ← h2, ← malfattiCircle_radius_formula]
  rfl

/-- Bridge for `ratio`: it is the ratio `ρ_i / r` of the `i`-th Malfatti radius to the inradius,
and also the ratio of the distances from vertex `i` to the circle's centre and to the incenter
(a homothety centred at the vertex). -/
theorem ratio_bridge (t : Triangle ℝ P) (i : Fin 3) :
    (malfattiCircle t i).radius / t.inradius = ratio t i ∧
      dist (t.points i) (malfattiCircle t i).center =
        ratio t i * dist (t.points i) t.incenter := by
  refine ⟨by rw [malfattiCircle_radius, mul_div_cancel_left₀ _ t.inradius_pos.ne'], ?_⟩
  rw [malfattiCircle_center, dist_left_lineMap, Real.norm_eq_abs, abs_of_pos (ratio_pos t i)]

/-- Bridge for `malfattiCircle`: the `i`-th circle has the defining properties of a Malfatti
circle: positive radius, tangent to both side lines through vertex `i` with its centre strictly on
the interior side of each, and externally tangent to the other two circles. -/
theorem malfattiCircle_bridge (t : Triangle ℝ P) (i : Fin 3) :
    0 < (malfattiCircle t i).radius ∧
      (∀ j k, i ≠ j → i ≠ k → j ≠ k →
        (malfattiCircle t i).IsTangent line[ℝ, t.points i, t.points j] ∧
        line[ℝ, t.points i, t.points j].SSameSide (malfattiCircle t i).center (t.points k)) ∧
      (∀ j, i ≠ j → (malfattiCircle t i).IsExtTangent (malfattiCircle t j)) :=
  ⟨malfattiCircle_radius_pos t i,
    fun _ _ hij hik hjk => ⟨(malfattiCircle_tangent_side t hij hik hjk).1.isTangent,
      (malfattiCircle_tangent_side t hij hik hjk).2⟩,
    fun _ h => malfattiCircle_isExtTangent t h⟩

end Malfatti
