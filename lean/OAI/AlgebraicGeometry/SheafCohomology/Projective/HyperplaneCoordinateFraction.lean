import OAI.AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions
import OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.CoordinateSectionMap

/-! # Hyperplane Coordinate Fraction -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.HyperplaneCoordinateFraction

noncomputable section

/-! The native hyperplane frame coefficient is exactly its homogeneous coordinate fraction. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra

theorem coordinateHyperplaneLocalEquation_eq_fraction {R σ : Type} [CommRing R] (i j : σ) :
    CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) i j =
      Divisors.LineBundles.Projective.CoordinateSectionMap.BundleCycles.projectiveCoordinateSection (MvPolynomial.homogeneousSubmodule σ R)
        (MvPolynomial.X i) (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X R i)
        (MvPolynomial.isHomogeneous_X R j) := by
  rw [CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation_eq_isLocalizationElem]
  change Proj.awayToSection (MvPolynomial.homogeneousSubmodule σ R) (MvPolynomial.X i) _ =
    Proj.awayToSection (MvPolynomial.homogeneousSubmodule σ R) (MvPolynomial.X i) _
  apply congrArg (Proj.awayToSection (MvPolynomial.homogeneousSubmodule σ R) (MvPolynomial.X i))
  apply HomogeneousLocalization.val_injective
  simp [HomogeneousLocalization.Away.isLocalizationElem, HomogeneousLocalization.Away.val_mk]

theorem projectiveCoordinateSection_appLE_of_eq
    {A B σ τ : Type} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ) (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (v t : A) (hv : v ∈ 𝒜 1) (ht : t ∈ 𝒜 1)
    (v' t' : B) (hv' : v' ∈ ℬ 1) (ht' : t' ∈ ℬ 1)
    (ev : f v = v') (et : f t = t') :
    (Proj.map f hf).appLE (Proj.basicOpen 𝒜 v) (Proj.basicOpen ℬ v')
      (by rw [← ev]; rfl) (Divisors.LineBundles.Projective.CoordinateSectionMap.BundleCycles.projectiveCoordinateSection 𝒜 v t hv ht) =
      Divisors.LineBundles.Projective.CoordinateSectionMap.BundleCycles.projectiveCoordinateSection ℬ v' t' hv' ht' := by
  subst v'
  subst t'
  change (Proj.map f hf).appLE (Proj.basicOpen 𝒜 v)
    (Proj.map f hf ⁻¹ᵁ Proj.basicOpen 𝒜 v) le_rfl
      (Divisors.LineBundles.Projective.CoordinateSectionMap.BundleCycles.projectiveCoordinateSection 𝒜 v t hv ht) = _
  rw [Scheme.Hom.appLE_eq_app]
  exact Divisors.LineBundles.Projective.CoordinateSectionMap.BundleCycles.projectiveCoordinateSection_map f hf v t hv ht

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.HyperplaneCoordinateFraction
