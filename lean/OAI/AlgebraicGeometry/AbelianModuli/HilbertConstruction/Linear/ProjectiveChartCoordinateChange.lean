import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Linear.ProjectiveFractionCoordinates

/-! # Projective Chart Coordinate Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Linear.ProjectiveChartCoordinateChange

noncomputable section

/-! On an overlap where a transformed coordinate is a unit, a linear
projective automorphism acts by the expected normalized linear coordinates. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] {X : Scheme.{u}} {n : ℕ}

private theorem degreeOneFractionMaps_eq
    (c : R →+* Γ(X, ⊤)) (v : Fin (n + 1) → Γ(X, ⊤)) (f g : Projective.ProjectivePresentations.coordinateRing R n)
    (hf : f ∈ Projective.ProjectivePresentations.coordinateGrading R n 1) (hg : g ∈ Projective.ProjectivePresentations.coordinateGrading R n 1)
    (hfu : IsUnit (MvPolynomial.eval₂Hom c v f)) (hgu : IsUnit (MvPolynomial.eval₂Hom c v g)) :
    Chart.OverlapMaps.projectiveFractionMap c v f hfu 1 hf Nat.zero_lt_one =
      Chart.OverlapMaps.projectiveFractionMap c v g hgu 1 hg Nat.zero_lt_one := by
  have hu : IsUnit (MvPolynomial.eval₂Hom c v (f * g)) :=
    (map_mul (MvPolynomial.eval₂Hom c v) f g).symm ▸ hfu.mul hgu
  exact (Chart.OverlapMaps.projectiveFractionMap_awayMap c v f g (f * g) 1 1 hf hg Nat.zero_lt_one rfl hfu hu).trans
    (Chart.OverlapMaps.projectiveFractionMap_awayMap c v g f (f * g) 1 1 hg hf Nat.zero_lt_one (mul_comm f g) hgu hu).symm

theorem projectiveChartMap_linearCoordinates
    (e : (Fin (n + 1) →₀ R) ≃ₗ[R] (Fin (n + 1) →₀ R))
    (c : R →+* Γ(X, ⊤)) (v : Fin (n + 1) → Γ(X, ⊤))
    (i j : Fin (n + 1)) (hi : v i = 1) (a : Γ(X, ⊤)ˣ)
    (hj : GradedCoordinateEvaluation.gradedCoordinateValues (GradedLinearCoordinateIsomorphism.gradedLinearCoordinateMap e.symm.toLinearMap) c v j = a) :
    ProjectiveChart.Evaluation.projectiveChartMap c v i hi ≫ (Relative.LinearCoordinateIsomorphism.affineLinearCoordinateIso n e).hom.left =
      ProjectiveChart.Evaluation.projectiveChartMap c
        (fun k => (↑a⁻¹ : Γ(X, ⊤)) *
          GradedCoordinateEvaluation.gradedCoordinateValues (GradedLinearCoordinateIsomorphism.gradedLinearCoordinateMap e.symm.toLinearMap) c v k)
        j (Chart.OverlapRings.normalizedCoordinate_eq_one _ j a hj) := by
  let g := GradedLinearCoordinateIsomorphism.gradedLinearCoordinateMap e.symm.toLinearMap
  let w := GradedCoordinateEvaluation.gradedCoordinateValues g c v
  have hui : IsUnit (MvPolynomial.eval₂Hom c v (MvPolynomial.X i)) :=
    ((MvPolynomial.eval₂Hom_X' c v i).trans hi).symm ▸ isUnit_one
  have huj : IsUnit (MvPolynomial.eval₂Hom c w (MvPolynomial.X j)) :=
    ((MvPolynomial.eval₂Hom_X' c w j).trans hj).symm ▸ a.isUnit
  have hug : IsUnit (MvPolynomial.eval₂Hom c v (g (MvPolynomial.X j))) :=
    (show MvPolynomial.eval₂Hom c v (g (MvPolynomial.X j)) = a from hj).symm ▸ a.isUnit
  have h₁ := degreeOneFractionMaps_eq c v (MvPolynomial.X i) (g (MvPolynomial.X j))
    (MvPolynomial.isHomogeneous_X R i) (g.map_mem (MvPolynomial.isHomogeneous_X R j)) hui hug
  have h₂ := ProjectiveFractionCoordinates.affineLinearCoordinateIso_fraction e c v (MvPolynomial.X j) 1
    (MvPolynomial.isHomogeneous_X R j) Nat.zero_lt_one huj hug
  have h₃ : Chart.OverlapMaps.projectiveFractionMap c w (MvPolynomial.X j) huj 1
      (MvPolynomial.isHomogeneous_X R j) Nat.zero_lt_one =
      ProjectiveChart.Evaluation.projectiveChartMap c (fun k => (↑a⁻¹ : Γ(X, ⊤)) * w k) j
        (Chart.OverlapRings.normalizedCoordinate_eq_one w j a hj) :=
    congrArg (fun b => X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom b) ≫
      Proj.awayι (Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X R j) Nat.zero_lt_one)
      (Chart.OverlapRings.homogeneousFractionEvaluation_normalized c w j a hj huj)
  exact (congrArg (fun q => q ≫ (Relative.LinearCoordinateIsomorphism.affineLinearCoordinateIso n e).hom.left)
    ((Chart.OverlapMaps.projectiveChartMap_eq_fraction c v i hi hui).trans h₁)).trans (h₂.trans h₃)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Linear.ProjectiveChartCoordinateChange
