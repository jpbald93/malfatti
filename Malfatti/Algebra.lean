import Mathlib

/-!
# Algebraic core of the Malfatti circle construction

We parametrise a triangle by `r` (inradius) and the numbers `p = tan (A/4)` etc.
(here introduced purely algebraically).  The tangent length from a vertex is
`X r p = r (1 - p²) / (2p)` and the distance from the incenter is `D r p = r (1 + p²) / (2p)`.
-/

namespace Malfatti

/-- Tangent length `s - a` in terms of the parameter `p`. -/
noncomputable def X (r t : ℝ) : ℝ := r * (1 - t ^ 2) / (2 * t)

/-- Distance vertex–incenter in terms of the parameter `p`. -/
noncomputable def D (r t : ℝ) : ℝ := r * (1 + t ^ 2) / (2 * t)

/-- The angle relation `A/4 + B/4 + C/4 = π/4` in tangent form. -/
def K (p q w : ℝ) : ℝ := 1 - p - q - w - p * q - q * w - w * p + p * q * w

/-- Ratio `ρ_A / r` of the Malfatti radius to the inradius. -/
noncomputable def mu (p q w : ℝ) : ℝ := (1 + q) * (1 + w) / (2 * (1 + p))

lemma mu_comm (p q w : ℝ) : mu p q w = mu p w q := by
  unfold mu; ring

lemma K_perm₁ (p q w : ℝ) : K p q w = K q w p := by unfold K; ring

/-- Heron's relation `r² s = (s-a)(s-b)(s-c)` forces the tangent relation `K = 0`. -/
lemma K_eq_zero_of_heron {r p q w : ℝ} (hr : 0 < r) (hp0 : 0 < p) (hp1 : p < 1)
    (hq0 : 0 < q) (hq1 : q < 1) (hw0 : 0 < w) (hw1 : w < 1)
    (h : r ^ 2 * (X r p + X r q + X r w) = X r p * X r q * X r w) : K p q w = 0 := by
  have hK2 : p * q * w + p * q + p * w - p + q * w - q - w - 1 < 0 := by
    nlinarith [mul_pos hp0 (sub_pos.2 hq1), mul_pos hw0 (sub_pos.2 hp1),
      mul_pos hq0 (sub_pos.2 hw1), mul_pos (mul_pos hp0 hq0) (sub_pos.2 hw1)]
  have key : r ^ 2 * (X r p + X r q + X r w) - X r p * X r q * X r w =
      K p q w * (p * q * w + p * q + p * w - p + q * w - q - w - 1) *
        (r ^ 3 / (8 * p * q * w)) := by
    unfold X K
    field_simp
    ring
  have h3 : 0 < r ^ 3 / (8 * p * q * w) := by positivity
  rw [h, sub_self] at key
  rcases mul_eq_zero.1 key.symm with h1 | h1
  · rcases mul_eq_zero.1 h1 with h2 | h2
    · exact h2
    · linarith
  · linarith

/-- The classical Malfatti radius formula, in parametrised form. -/
lemma radius_eq {r p q w : ℝ} (hr : 0 < r) (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q)
    (hw0 : 0 < w) (hK : K p q w = 0) :
    r / (2 * X r p) * ((X r p + X r q + X r w) - r - (D r q + D r w - D r p)) =
      r * mu p q w := by
  have h1 : (1 - p) ≠ 0 := by linarith
  have h2 : (1 + p) ≠ 0 := by linarith
  have h3 : (1 - p ^ 2) ≠ 0 := by nlinarith
  have key : r / (2 * X r p) * ((X r p + X r q + X r w) - r - (D r q + D r w - D r p)) -
      r * mu p q w = K p q w * (r / (2 * (1 - p) * (1 + p))) := by
    unfold X D K mu
    field_simp
    ring
  rw [hK, zero_mul, sub_eq_zero] at key
  exact key

/-- The pairwise external tangency identity
`|O_A O_B|² = (ρ_A + ρ_B)²`, in parametrised form. -/
lemma dist_identity {r p q w : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q)
    (hK : K p q w = 0) :
    (1 - mu p q w) ^ 2 * (X r p ^ 2 + r ^ 2) + (1 - mu q w p) ^ 2 * (X r q ^ 2 + r ^ 2) -
        2 * (1 - mu p q w) * (1 - mu q w p) * (r ^ 2 - X r p * X r q) =
      (r * mu p q w + r * mu q w p) ^ 2 := by
  have h2 : (1 + p) ≠ 0 := by linarith
  have h3 : (1 + q) ≠ 0 := by linarith
  have key : (1 - mu p q w) ^ 2 * (X r p ^ 2 + r ^ 2) + (1 - mu q w p) ^ 2 * (X r q ^ 2 + r ^ 2) -
        2 * (1 - mu p q w) * (1 - mu q w p) * (r ^ 2 - X r p * X r q) -
      (r * mu p q w + r * mu q w p) ^ 2 =
      K p q w * (r ^ 2 * (p + q) * (p^2*q*w - p^2*q - p^2*w - p^2 + p*q^2*w - p*q^2
        + 6*p*q*w + 6*p*q - p*w + p - q^2*w - q^2 - q*w + q) / (16 * p ^ 2 * q ^ 2)) := by
    unfold X K mu
    field_simp
    ring
  rw [hK, zero_mul, sub_eq_zero] at key
  exact key

lemma mu_pos {p q w : ℝ} (hp0 : 0 < p) (hq0 : 0 < q) (hw0 : 0 < w) : 0 < mu p q w := by
  unfold mu; positivity

lemma mu_lt_one {p q w : ℝ} (hp0 : 0 < p) (hq0 : 0 < q) (hq1 : q < 1) (hw0 : 0 < w)
    (hw1 : w < 1) (hK : K p q w = 0) : mu p q w < 1 := by
  have hm : 0 < 1 + q + w - q * w := by nlinarith [mul_pos hq0 (sub_pos.2 hw1)]
  have h : (2 * (1 + p) - (1 + q) * (1 + w)) * (1 + q + w - q * w) =
      p * (1 + q + w - q * w) * (3 + q + w - q * w) := by
    unfold K at hK
    linear_combination (1 + q + w - q * w) * hK
  have hpos : 0 < p * (1 + q + w - q * w) * (3 + q + w - q * w) :=
    mul_pos (mul_pos hp0 hm) (by nlinarith [mul_pos hq0 (sub_pos.2 hw1)])
  have hA : 0 < 2 * (1 + p) - (1 + q) * (1 + w) := by nlinarith
  unfold mu
  rw [div_lt_one (by positivity)]
  linarith

/-- Recover the parameter from a tangent length `x` and distance `d` with `d² = x² + r²`. -/
lemma param_spec {r d x : ℝ} (hr : 0 < r) (hx : 0 < x) (hd0 : 0 < d) (hd : d ^ 2 = x ^ 2 + r ^ 2) :
    0 < (d - x) / r ∧ (d - x) / r < 1 ∧ x = X r ((d - x) / r) ∧ d = D r ((d - x) / r) := by
  have hdx : 0 < d - x := by nlinarith
  have hdx1 : d - x < r := by nlinarith
  set p := (d - x) / r with hp
  have hp0 : 0 < p := div_pos hdx hr
  have hpr : p * r = d - x := by rw [hp]; field_simp
  refine ⟨hp0, (div_lt_one hr).2 hdx1, ?_, ?_⟩
  · unfold X
    rw [eq_div_iff (by positivity)]
    apply mul_left_cancel₀ hr.ne'
    linear_combination (p * r + d + x) * hpr + hd
  · unfold D
    rw [eq_div_iff (by positivity)]
    apply mul_left_cancel₀ hr.ne'
    linear_combination (x + d - p * r) * hpr + hd

end Malfatti
