import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.ProjectiveMaps

/-! # Rescaling -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveCoordinate.Rescaling

noncomputable section

/-! A cross-multiplication criterion for equality of normalized projective-coordinate maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {T : Scheme.{u}} {n : ℕ}

theorem projectiveChartMap_eq_of_cross (c : R →+* Γ(T, ⊤))
    (v w : Fin (n + 1) → Γ(T, ⊤)) (i j : Fin (n + 1))
    (hi : v i = 1) (hj : w j = 1) (hu : IsUnit (v j))
    (hcross : ∀ k, v j * w k = v k) :
    ProjectiveChart.Evaluation.projectiveChartMap c v i hi = ProjectiveChart.Evaluation.projectiveChartMap c w j hj := by
  let a : Γ(T, ⊤)ˣ := hu.unit
  have ha : v j = a := hu.unit_spec.symm
  have hw : (fun k => (↑a⁻¹ : Γ(T, ⊤)) * v k) = w := by
    funext k
    rw [← hcross k, ha, ← mul_assoc, a.inv_mul, one_mul]
  exact (Chart.OverlapMaps.projectiveChartMap_normalize c v i j hi a ha).trans
    (Framed.ProjectiveMaps.projectiveChartMap_congr c hw j _ hj)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveCoordinate.Rescaling
