import Malfatti.Geometry

/-!
# Main statement in the Euclidean plane `EuclideanSpace ℝ (Fin 2)`
-/

open EuclideanGeometry Affine

namespace Malfatti

/-- **Existence of the Malfatti circles.** In every (nondegenerate) triangle in the Euclidean
plane there are three circles of positive radius such that circle `i` is tangent to the two side
lines through vertex `i`, with its centre strictly on the interior side of each, and any two of
the circles are externally tangent. -/
theorem malfatti_circles_exist (t : Triangle ℝ (EuclideanSpace ℝ (Fin 2))) :
    ∃ c : Fin 3 → Sphere (EuclideanSpace ℝ (Fin 2)),
      (∀ i, 0 < (c i).radius) ∧
      (∀ i j k, i ≠ j → i ≠ k → j ≠ k →
        (c i).IsTangent line[ℝ, t.points i, t.points j] ∧
        line[ℝ, t.points i, t.points j].SSameSide (c i).center (t.points k)) ∧
      (∀ i j, i ≠ j → (c i).IsExtTangent (c j)) := by
  have : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) := ⟨finrank_euclideanSpace_fin⟩
  refine ⟨malfattiCircle t, fun i => malfattiCircle_radius_pos t i,
    fun i j k hij hik hjk => ?_, fun i j h => malfattiCircle_isExtTangent t h⟩
  obtain ⟨h1, h2⟩ := malfattiCircle_tangent_side t hij hik hjk
  exact ⟨h1.isTangent, h2⟩

/-- **Malfatti circles with the classical radius formula**, in the plane: the circles of
`malfatti_circles_exist` can be taken with radii
`ρ_i = r / (2 (s - a_i)) * (s - r - (I A_{i+1} + I A_{i+2} - I A_i))`. -/
theorem malfatti_circles_formula (t : Triangle ℝ (EuclideanSpace ℝ (Fin 2))) :
    ∃ c : Fin 3 → Sphere (EuclideanSpace ℝ (Fin 2)),
      (∀ i, (c i).radius =
        t.inradius / (2 * (semi t - dist (t.points (i + 1)) (t.points (i + 2)))) *
          (semi t - t.inradius - (dist t.incenter (t.points (i + 1)) +
            dist t.incenter (t.points (i + 2)) - dist t.incenter (t.points i)))) ∧
      (∀ i, 0 < (c i).radius) ∧
      (∀ i j k, i ≠ j → i ≠ k → j ≠ k →
        (c i).IsTangent line[ℝ, t.points i, t.points j] ∧
        line[ℝ, t.points i, t.points j].SSameSide (c i).center (t.points k)) ∧
      (∀ i j, i ≠ j → (c i).IsExtTangent (c j)) := by
  have : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) := ⟨finrank_euclideanSpace_fin⟩
  refine ⟨malfattiCircle t, fun i => malfattiCircle_radius_formula t i,
    fun i => malfattiCircle_radius_pos t i,
    fun i j k hij hik hjk => ?_, fun i j h => malfattiCircle_isExtTangent t h⟩
  obtain ⟨h1, h2⟩ := malfattiCircle_tangent_side t hij hik hjk
  exact ⟨h1.isTangent, h2⟩

end Malfatti
