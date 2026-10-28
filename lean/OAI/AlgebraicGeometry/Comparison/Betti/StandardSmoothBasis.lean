import OAI.AlgebraicGeometry.Comparison.Betti.StandardSmoothOpens
import OAI.AlgebraicGeometry.Comparison.Betti.Open.AffineIsoEvaluation
import OAI.AlgebraicGeometry.Comparison.Betti.Affine.ExteriorRestrictions

/-! # Standard Smooth Basis -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.StandardSmoothBasis

noncomputable section

section

/-! The standard smooth neighborhoods have their actual open subschemes and scalar structures. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)

attribute [local instance] Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra

def openSectionTopAlgEquiv (U : X.left.Opens) :
    Γ(X.left, U) ≃ₐ[ℂ] Affine.ExteriorRestrictions.globalCoordinateAlgebra (Open.AffineIsoEvaluation.openOver X U) :=
  AlgEquiv.ofBijective (Open.AffineIsoEvaluation.openSectionTopAlgHom X U) (ConcreteCategory.bijective_of_isIso U.topIso.inv)

theorem standardSmooth_openOver (U : X.left.Opens)
    [Algebra.IsStandardSmooth ℂ Γ(X.left, U)] :
    Algebra.IsStandardSmooth ℂ (Affine.ExteriorRestrictions.globalCoordinateAlgebra (Open.AffineIsoEvaluation.openOver X U)) :=
  Algebra.IsStandardSmooth.of_algEquiv (openSectionTopAlgEquiv X U)

theorem exists_standardSmooth_openOver [Smooth X.hom] (x : X.left) :
    ∃ (U : X.left.Opens), x ∈ U ∧ IsAffine (Open.AffineIsoEvaluation.openOver X U).left ∧
      Algebra.IsStandardSmooth ℂ (Affine.ExteriorRestrictions.globalCoordinateAlgebra (Open.AffineIsoEvaluation.openOver X U)) := by
  obtain ⟨U, hU, hx, hstd⟩ := StandardSmoothOpens.exists_standardSmooth_affineOpen X x
  have : Algebra.IsStandardSmooth ℂ Γ(X.left, U) := hstd
  exact ⟨U, hx, hU, standardSmooth_openOver X U⟩

end

/-! Standard smooth affine neighborhoods form a basis on the actual Zariski space. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)

attribute [local instance] Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra

theorem standardSmooth_section_basicOpen (U : X.left.Opens) (hU : IsAffineOpen U)
    [Algebra.IsStandardSmooth ℂ Γ(X.left, U)] (r : Γ(X.left, U)) :
    Algebra.IsStandardSmooth ℂ Γ(X.left, X.left.basicOpen r) := by
  let i : op U ⟶ op (X.left.basicOpen r) := (homOfLE (X.left.basicOpen_le r)).op
  let g : Γ(X.left, U) →ₐ[ℂ] Γ(X.left, X.left.basicOpen r) :=
    ((Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras ℂ X).map i).hom
  let := g.toRingHom.toAlgebra
  have : IsLocalization.Away r Γ(X.left, X.left.basicOpen r) :=
    hU.isLocalization_of_eq_basicOpen r (homOfLE (X.left.basicOpen_le r)) rfl
  have : Algebra.IsStandardSmooth Γ(X.left, U) Γ(X.left, X.left.basicOpen r) :=
    Algebra.IsStandardSmooth.localization_away r
  exact Algebra.IsStandardSmooth.trans ℂ Γ(X.left, U) Γ(X.left, X.left.basicOpen r)

theorem exists_standardSmooth_openOver_le [Smooth X.hom]
    (W : X.left.Opens) (x : W) :
    ∃ (U : X.left.Opens), U ≤ W ∧ (x : X.left) ∈ U ∧ IsAffine (Open.AffineIsoEvaluation.openOver X U).left ∧
      Algebra.IsStandardSmooth ℂ (Affine.ExteriorRestrictions.globalCoordinateAlgebra (Open.AffineIsoEvaluation.openOver X U)) := by
  obtain ⟨V, hV, hxV, hstd⟩ := StandardSmoothOpens.exists_standardSmooth_affineOpen X x
  have : Algebra.IsStandardSmooth ℂ Γ(X.left, V) := hstd
  obtain ⟨r, hrW, hxr⟩ := hV.exists_basicOpen_le x hxV
  have : Algebra.IsStandardSmooth ℂ Γ(X.left, X.left.basicOpen r) :=
    standardSmooth_section_basicOpen X V hV r
  exact ⟨X.left.basicOpen r, hrW, hxr, hV.basicOpen r, standardSmooth_openOver X _⟩

end

end OAI.AlgebraicGeometry.Comparison.Betti.StandardSmoothBasis
