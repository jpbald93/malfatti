import Malfatti.Algebra

/-!
# Malfatti circles of a triangle

For a triangle `t` with incenter `I` and inradius `r`, the `i`-th Malfatti circle has centre
on the segment from vertex `i` to `I` (the internal bisector) at ratio `ratio t i`, and radius
`r * ratio t i`.  We prove that it is tangent to the two sides through vertex `i` (with centre
on the interior side) and externally tangent to the other two Malfatti circles, and that the
radius equals Malfatti's classical formula `r / (2 (s - a)) * (s - r - (IB + IC - IA))`.
-/

open EuclideanGeometry Affine AffineMap
open scoped RealInnerProductSpace

namespace Malfatti

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- Tangent length from vertex `i` to the incircle. -/
noncomputable def tl (t : Triangle ℝ P) (i : Fin 3) : ℝ :=
  √(dist (t.points i) t.incenter ^ 2 - t.inradius ^ 2)

/-- The parameter `tan (A_i / 4)`, defined metrically. -/
noncomputable def tparam (t : Triangle ℝ P) (i : Fin 3) : ℝ :=
  (dist (t.points i) t.incenter - tl t i) / t.inradius

/-- Ratio of the `i`-th Malfatti radius to the inradius. -/
noncomputable def ratio (t : Triangle ℝ P) (i : Fin 3) : ℝ :=
  mu (tparam t i) (tparam t (i + 1)) (tparam t (i + 2))

/-- The `i`-th Malfatti circle: centre on the segment from vertex `i` to the incenter. -/
noncomputable def malfattiCircle (t : Triangle ℝ P) (i : Fin 3) : Sphere P :=
  ⟨lineMap (t.points i) t.incenter (ratio t i), t.inradius * ratio t i⟩

/-- Semiperimeter. -/
noncomputable def semi (t : Triangle ℝ P) : ℝ :=
  (dist (t.points 0) (t.points 1) + dist (t.points 1) (t.points 2) +
    dist (t.points 2) (t.points 0)) / 2

lemma malfattiCircle_radius (t : Triangle ℝ P) (i : Fin 3) :
    (malfattiCircle t i).radius = t.inradius * ratio t i := rfl

lemma malfattiCircle_center (t : Triangle ℝ P) (i : Fin 3) :
    (malfattiCircle t i).center = lineMap (t.points i) t.incenter (ratio t i) := rfl

lemma fin3_distinct (i : Fin 3) : i ≠ i + 1 ∧ i ≠ i + 2 ∧ i + 1 ≠ i + 2 := by
  revert i; decide

lemma fin3_add (i : Fin 3) : i + 1 + 1 = i + 2 ∧ i + 1 + 2 = i := by
  revert i; decide

lemma fin3_third {i j : Fin 3} (h : i ≠ j) : ∃ k, i ≠ k ∧ j ≠ k := by
  revert i j; decide

lemma sum_cyc (f : Fin 3 → ℝ) (i : Fin 3) : f i + f (i + 1) + f (i + 2) = f 0 + f 1 + f 2 := by
  have h := Fintype.sum_equiv (Equiv.addRight i) (fun j => f (j + i)) f (fun _ => rfl)
  simp only [Fin.sum_univ_three, zero_add] at h
  rw [add_comm (1 : Fin 3) i, add_comm (2 : Fin 3) i] at h
  exact h

lemma lineMap_vsub_lineMap_same (a b c : P) (μ : ℝ) :
    lineMap a b μ -ᵥ lineMap a c μ = μ • (b -ᵥ c) := by
  rw [lineMap_apply, lineMap_apply, vadd_vsub_vadd_cancel_right, ← smul_sub,
    vsub_sub_vsub_cancel_right]

section Geometry

variable (t : Triangle ℝ P)

lemma touch_mem {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) :
    Sbtw ℝ (t.points i₁) (t.touchpoint ∅ i₃) (t.points i₂) :=
  t.sbtw_touchpoint_empty h₁₃ h₁₂ h₂₃.symm

lemma dist_touch_incenter (i : Fin 3) : dist (t.touchpoint ∅ i) t.incenter = t.inradius := by
  have h := t.touchpoint_mem_insphere i
  rwa [EuclideanGeometry.mem_sphere, Simplex.insphere_center, Simplex.insphere_radius] at h

variable [Fact (Module.finrank ℝ V = 2)]

lemma perp {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) {y : P}
    (hy : y ∈ line[ℝ, t.points i₁, t.points i₂]) :
    ⟪y -ᵥ t.touchpoint ∅ i₃, t.touchpoint ∅ i₃ -ᵥ t.incenter⟫ = 0 := by
  rw [t.affineSpan_pair_eq_orthRadius_insphere h₁₃.symm h₂₃.symm h₁₂,
    Sphere.mem_orthRadius_iff_inner_left, Simplex.insphere_center] at hy
  exact hy

lemma dist_sq_split {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) :
    dist (t.points i₁) t.incenter ^ 2 =
      dist (t.points i₁) (t.touchpoint ∅ i₃) ^ 2 + t.inradius ^ 2 := by
  have hp := perp t h₁₂ h₁₃ h₂₃ (left_mem_affineSpan_pair ℝ _ _)
  have hsplit : t.points i₁ -ᵥ t.incenter =
      (t.points i₁ -ᵥ t.touchpoint ∅ i₃) + (t.touchpoint ∅ i₃ -ᵥ t.incenter) :=
    (vsub_add_vsub_cancel _ _ _).symm
  rw [← dist_touch_incenter t i₃, dist_eq_norm_vsub V, dist_eq_norm_vsub V,
    dist_eq_norm_vsub V, hsplit, norm_add_sq_real, hp]
  ring

lemma tl_eq_dist {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) :
    dist (t.points i₁) (t.touchpoint ∅ i₃) = tl t i₁ := by
  unfold tl
  rw [dist_sq_split t h₁₂ h₁₃ h₂₃, add_sub_cancel_right, Real.sqrt_sq dist_nonneg]

lemma tl_pos (i : Fin 3) : 0 < tl t i := by
  obtain ⟨h1, h2, h3⟩ := fin3_distinct i
  rw [← tl_eq_dist t h1 h2 h3]
  exact dist_pos.2 (touch_mem t h1 h2 h3).left_ne

lemma dist_vertex_sq (i : Fin 3) :
    dist (t.points i) t.incenter ^ 2 = tl t i ^ 2 + t.inradius ^ 2 := by
  obtain ⟨h1, h2, h3⟩ := fin3_distinct i
  rw [dist_sq_split t h1 h2 h3, tl_eq_dist t h1 h2 h3]

/-- Each side is the sum of the two tangent lengths from its endpoints. -/
lemma side_eq {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) :
    dist (t.points i₁) (t.points i₂) = tl t i₁ + tl t i₂ := by
  rw [← (touch_mem t h₁₂ h₁₃ h₂₃).wbtw.dist_add_dist, tl_eq_dist t h₁₂ h₁₃ h₂₃, dist_comm,
    tl_eq_dist t h₁₂.symm h₂₃ h₁₃]

lemma gram {i j : Fin 3} (h : i ≠ j) :
    ⟪t.points i -ᵥ t.incenter, t.points j -ᵥ t.incenter⟫ =
      t.inradius ^ 2 - tl t i * tl t j := by
  obtain ⟨k, hik, hjk⟩ := fin3_third h
  have hn : ‖(t.points i -ᵥ t.incenter) - (t.points j -ᵥ t.incenter)‖ ^ 2 =
      (tl t i + tl t j) ^ 2 := by
    rw [vsub_sub_vsub_cancel_right, ← dist_eq_norm_vsub V, side_eq t h hik hjk]
  rw [norm_sub_sq_real, ← dist_eq_norm_vsub V, ← dist_eq_norm_vsub V, dist_vertex_sq,
    dist_vertex_sq] at hn
  linear_combination (-1 / 2 : ℝ) * hn

/-- Heron's relation `r² s = (s-a)(s-b)(s-c)`, from the barycentric description of the
incenter and the Gram matrix of the vectors `A_i - I`. -/
lemma heron : t.inradius ^ 2 * (tl t 0 + tl t 1 + tl t 2) = tl t 0 * tl t 1 * tl t 2 := by
  have hw : ∑ i, t.excenterWeights ∅ i = 1 := t.excenterExists_empty.sum_excenterWeights_eq_one
  have hz : ∑ i, t.excenterWeights ∅ i • (t.points i -ᵥ t.incenter) = 0 := by
    rw [Finset.univ.sum_smul_vsub_const_eq_affineCombination_vsub _ _ _ hw]
    exact vsub_self _
  have e : ∀ j, ∑ i, t.excenterWeights ∅ i *
      ⟪t.points i -ᵥ t.incenter, t.points j -ᵥ t.incenter⟫ = 0 := by
    intro j
    have := congrArg (fun v => ⟪v, t.points j -ᵥ t.incenter⟫) hz
    simp only [sum_inner, real_inner_smul_left, inner_zero_left] at this
    exact this
  have hu : ∀ i, ⟪t.points i -ᵥ t.incenter, t.points i -ᵥ t.incenter⟫ =
      tl t i ^ 2 + t.inradius ^ 2 := by
    intro i
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm_vsub V, dist_vertex_sq]
  have e0 := e 0
  have e1 := e 1
  have e2 := e 2
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two] at e0 e1 e2 hw
  rw [hu 0, gram t (by decide : (1 : Fin 3) ≠ 0), gram t (by decide : (2 : Fin 3) ≠ 0)] at e0
  rw [hu 1, gram t (by decide : (0 : Fin 3) ≠ 1), gram t (by decide : (2 : Fin 3) ≠ 1)] at e1
  rw [hu 2, gram t (by decide : (0 : Fin 3) ≠ 2), gram t (by decide : (1 : Fin 3) ≠ 2)] at e2
  have hx := tl_pos t 0
  have hy := tl_pos t 1
  have hzz := tl_pos t 2
  set x := tl t 0
  set y := tl t 1
  set z := tl t 2
  set r := t.inradius
  have hT : x * y * z * (x * y * z - r ^ 2 * (x + y + z)) = 0 := by
    linear_combination (-(x * y * z * (x * y * z - r ^ 2 * (x + y + z)))) * hw +
      (-x * y ^ 2 * z / 2 - x * y * z ^ 2 / 2) * e0 +
      (-x ^ 2 * y * z / 2 - x * y * z ^ 2 / 2) * e1 +
      (-x ^ 2 * y * z / 2 - x * y ^ 2 * z / 2) * e2
  have hxyz : 0 < x * y * z := mul_pos (mul_pos hx hy) hzz
  rcases mul_eq_zero.1 hT with h | h
  · exact absurd h hxyz.ne'
  · linarith

lemma tparam_spec (i : Fin 3) :
    0 < tparam t i ∧ tparam t i < 1 ∧ tl t i = X t.inradius (tparam t i) ∧
      dist (t.points i) t.incenter = D t.inradius (tparam t i) :=
  param_spec t.inradius_pos (tl_pos t i) (dist_pos.2 (t.incenter_ne_point i).symm)
    (dist_vertex_sq t i)

lemma K_zero : K (tparam t 0) (tparam t 1) (tparam t 2) = 0 := by
  obtain ⟨a0, b0, c0, -⟩ := tparam_spec t 0
  obtain ⟨a1, b1, c1, -⟩ := tparam_spec t 1
  obtain ⟨a2, b2, c2, -⟩ := tparam_spec t 2
  apply K_eq_zero_of_heron t.inradius_pos a0 b0 a1 b1 a2 b2
  rw [← c0, ← c1, ← c2]
  exact heron t

lemma K_cyc (i : Fin 3) : K (tparam t i) (tparam t (i + 1)) (tparam t (i + 2)) = 0 := by
  have h0 := K_zero t
  have h1 : K (tparam t 1) (tparam t 2) (tparam t 0) = 0 := by rw [← K_perm₁]; exact h0
  have h2 : K (tparam t 2) (tparam t 0) (tparam t 1) = 0 := by rw [← K_perm₁]; exact h1
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

lemma ratio_pos (i : Fin 3) : 0 < ratio t i :=
  mu_pos (tparam_spec t i).1 (tparam_spec t (i + 1)).1 (tparam_spec t (i + 2)).1

lemma ratio_lt_one (i : Fin 3) : ratio t i < 1 :=
  mu_lt_one (tparam_spec t i).1 (tparam_spec t (i + 1)).1 (tparam_spec t (i + 1)).2.1
    (tparam_spec t (i + 2)).1 (tparam_spec t (i + 2)).2.1 (K_cyc t i)

/-- A circle centred on the segment from vertex `i₁` to the incenter, at ratio `μ`, with radius
`μ r`, is tangent to the side line through `i₁, i₂`. -/
lemma isTangentAt_side {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃)
    {μ : ℝ} (hμ : 0 ≤ μ) :
    (⟨lineMap (t.points i₁) t.incenter μ, t.inradius * μ⟩ : Sphere P).IsTangentAt
      (lineMap (t.points i₁) (t.touchpoint ∅ i₃) μ) line[ℝ, t.points i₁, t.points i₂] := by
  have hT : t.touchpoint ∅ i₃ ∈ line[ℝ, t.points i₁, t.points i₂] :=
    (touch_mem t h₁₂ h₁₃ h₂₃).wbtw.mem_affineSpan
  have hP : lineMap (t.points i₁) (t.touchpoint ∅ i₃) μ ∈ line[ℝ, t.points i₁, t.points i₂] :=
    AffineMap.lineMap_mem μ (left_mem_affineSpan_pair ℝ _ _) hT
  have hd := lineMap_vsub_lineMap_same (t.points i₁) (t.touchpoint ∅ i₃) t.incenter μ
  refine ⟨?_, hP, ?_⟩
  · rw [EuclideanGeometry.mem_sphere]
    change dist _ (lineMap (t.points i₁) t.incenter μ) = t.inradius * μ
    rw [dist_eq_norm_vsub V, hd, norm_smul, Real.norm_eq_abs, abs_of_nonneg hμ,
      ← dist_eq_norm_vsub V, dist_touch_incenter, mul_comm]
  · intro y hy
    rw [Sphere.mem_orthRadius_iff_inner_left]
    change ⟪_, _ -ᵥ lineMap (t.points i₁) t.incenter μ⟫ = 0
    rw [hd, real_inner_smul_right,
      ← vsub_sub_vsub_cancel_right y (lineMap (t.points i₁) (t.touchpoint ∅ i₃) μ)
        (t.touchpoint ∅ i₃), inner_sub_left, perp t h₁₂ h₁₃ h₂₃ hy, perp t h₁₂ h₁₃ h₂₃ hP]
    ring

omit [Fact (Module.finrank ℝ V = 2)] in
lemma sSameSide_center {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃)
    {μ : ℝ} (hμ : 0 < μ) :
    line[ℝ, t.points i₁, t.points i₂].SSameSide (lineMap (t.points i₁) t.incenter μ)
      (t.points i₃) :=
  (AffineSubspace.sSameSide_lineMap_left (left_mem_affineSpan_pair ℝ _ _)
    (t.incenter_notMem_affineSpan_pair i₁ i₂) hμ).trans
    (t.sSameSide_affineSpan_pair_incenter_point h₁₃.symm h₂₃.symm h₁₂)

/-- **Malfatti circles, side tangency.** The `i`-th Malfatti circle is tangent to the side line
through vertices `i, j`, and its centre lies strictly on the same side of that line as the
third vertex `k`. -/
theorem malfattiCircle_tangent_side {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (malfattiCircle t i).IsTangentAt (lineMap (t.points i) (t.touchpoint ∅ k) (ratio t i))
        line[ℝ, t.points i, t.points j] ∧
      line[ℝ, t.points i, t.points j].SSameSide (malfattiCircle t i).center (t.points k) :=
  ⟨isTangentAt_side t hij hik hjk (ratio_pos t i).le, sSameSide_center t hij hik hjk (ratio_pos t i)⟩

omit [Fact (Module.finrank ℝ V = 2)] in
lemma center_vsub_incenter (i : Fin 3) :
    (malfattiCircle t i).center -ᵥ t.incenter = (1 - ratio t i) • (t.points i -ᵥ t.incenter) :=
  lineMap_vsub_right _ _ _

lemma isExtTangent_succ (i : Fin 3) :
    (malfattiCircle t i).IsExtTangent (malfattiCircle t (i + 1)) := by
  obtain ⟨hd1, -, -⟩ := fin3_distinct i
  obtain ⟨ha1, ha2⟩ := fin3_add i
  obtain ⟨p0, p1, px, -⟩ := tparam_spec t i
  obtain ⟨q0, -, qx, -⟩ := tparam_spec t (i + 1)
  have hK := K_cyc t i
  have hri : ratio t i = mu (tparam t i) (tparam t (i + 1)) (tparam t (i + 2)) := rfl
  have hrj : ratio t (i + 1) = mu (tparam t (i + 1)) (tparam t (i + 2)) (tparam t i) := by
    unfold ratio; rw [ha1, ha2]
  have hmi := ratio_pos t i
  have hmj := ratio_pos t (i + 1)
  have hr := t.inradius_pos
  rw [Sphere.isExtTangent_iff_dist_center, malfattiCircle_radius, malfattiCircle_radius]
  refine ⟨?_, by positivity, by positivity⟩
  have key := dist_identity (r := t.inradius) p0 p1 q0 hK
  rw [← hri, ← hrj] at key
  have hsq : dist (malfattiCircle t i).center (malfattiCircle t (i + 1)).center ^ 2 =
      (t.inradius * ratio t i + t.inradius * ratio t (i + 1)) ^ 2 := by
    rw [dist_eq_norm_vsub V, ← vsub_sub_vsub_cancel_right _ _ t.incenter,
      center_vsub_incenter, center_vsub_incenter, norm_sub_sq_real, norm_smul, norm_smul,
      real_inner_smul_left, real_inner_smul_right, mul_pow, mul_pow, Real.norm_eq_abs,
      Real.norm_eq_abs, sq_abs, sq_abs, ← dist_eq_norm_vsub V, ← dist_eq_norm_vsub V,
      dist_vertex_sq, dist_vertex_sq, gram t hd1, px, qx]
    linear_combination key
  exact (pow_left_inj₀ dist_nonneg (by positivity) two_ne_zero).1 hsq

/-- **Malfatti circles, mutual tangency.** Any two distinct Malfatti circles are externally
tangent. -/
theorem malfattiCircle_isExtTangent {i j : Fin 3} (h : i ≠ j) :
    (malfattiCircle t i).IsExtTangent (malfattiCircle t j) := by
  have : j = i + 1 ∨ i = j + 1 := by revert i j; decide
  rcases this with rfl | rfl
  · exact isExtTangent_succ t i
  · exact (isExtTangent_succ t j).symm

lemma malfattiCircle_radius_pos (i : Fin 3) : 0 < (malfattiCircle t i).radius :=
  mul_pos t.inradius_pos (ratio_pos t i)

lemma malfattiCircle_radius_lt_inradius (i : Fin 3) :
    (malfattiCircle t i).radius < t.inradius := by
  rw [malfattiCircle_radius]
  have := ratio_lt_one t i
  have := t.inradius_pos
  nlinarith

/-- **Malfatti's radius formula**: `ρ_A = r / (2 (s - a)) * (s - r - (IB + IC - IA))`. -/
theorem malfattiCircle_radius_formula (i : Fin 3) :
    (malfattiCircle t i).radius =
      t.inradius / (2 * (semi t - dist (t.points (i + 1)) (t.points (i + 2)))) *
        (semi t - t.inradius - (dist t.incenter (t.points (i + 1)) +
          dist t.incenter (t.points (i + 2)) - dist t.incenter (t.points i))) := by
  obtain ⟨hd1, hd2, hd3⟩ := fin3_distinct i
  have hs : semi t = tl t i + tl t (i + 1) + tl t (i + 2) := by
    rw [sum_cyc (tl t) i]
    unfold semi
    rw [side_eq t (by decide : (0 : Fin 3) ≠ 1) (by decide : (0 : Fin 3) ≠ 2)
        (by decide : (1 : Fin 3) ≠ 2),
      side_eq t (by decide : (1 : Fin 3) ≠ 2) (by decide : (1 : Fin 3) ≠ 0)
        (by decide : (2 : Fin 3) ≠ 0),
      side_eq t (by decide : (2 : Fin 3) ≠ 0) (by decide : (2 : Fin 3) ≠ 1)
        (by decide : (0 : Fin 3) ≠ 1)]
    ring
  have ha : dist (t.points (i + 1)) (t.points (i + 2)) = tl t (i + 1) + tl t (i + 2) :=
    side_eq t hd3 hd1.symm hd2.symm
  obtain ⟨p0, p1, px, pd⟩ := tparam_spec t i
  obtain ⟨q0, -, qx, qd⟩ := tparam_spec t (i + 1)
  obtain ⟨w0, -, wx, wd⟩ := tparam_spec t (i + 2)
  rw [hs, ha, dist_comm t.incenter, dist_comm t.incenter, dist_comm t.incenter, pd, qd, wd,
    px, qx, wx, malfattiCircle_radius,
    show X t.inradius (tparam t i) + X t.inradius (tparam t (i + 1)) +
        X t.inradius (tparam t (i + 2)) -
        (X t.inradius (tparam t (i + 1)) + X t.inradius (tparam t (i + 2))) =
        X t.inradius (tparam t i) by ring]
  exact (radius_eq t.inradius_pos p0 p1 q0 w0 (K_cyc t i)).symm

end Geometry

end Malfatti
