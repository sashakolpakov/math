import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.SectionSheaf
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.CoefficientRestriction
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.Presheaf

/-! # Open Domain Sheaf -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.OpenDomainSheaf

noncomputable section

/-! The actual holomorphic-form presheaf on a coordinate space is the genuine holomorphic section sheaf. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

def holomorphicPureSectionComplexEquiv (U : Opens E) (n : ℕ) :
    CoefficientMem.holomorphicOpenCoefficients U n ≃ₗ[ℂ] CoefficientMem.holomorphicSections U (Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule E n 0) where
  toFun := FunctionPure.holomorphicPureSectionEquiv U n
  invFun := (FunctionPure.holomorphicPureSectionEquiv U n).symm
  left_inv := (FunctionPure.holomorphicPureSectionEquiv U n).left_inv
  right_inv := (FunctionPure.holomorphicPureSectionEquiv U n).right_inv
  map_add' := (FunctionPure.holomorphicPureSectionEquiv U n).map_add
  map_smul' c a := by
    apply Subtype.ext
    funext x
    apply Subtype.ext
    rfl

def holomorphicFormSectionEquiv (U : Opens E) (n : ℕ) :
    DeRhamComplex.forms E U n ≃ₗ[ℂ] CoefficientMem.holomorphicSections U (Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule E n 0) :=
  (CoefficientMem.holomorphicCoefficientsEquivForms U n).symm.trans (holomorphicPureSectionComplexEquiv U n)

theorem holomorphicFormSectionEquiv_restrict {U V : Opens E} (h : V ≤ U) (n : ℕ)
    (a : DeRhamComplex.forms E U n) :
    holomorphicFormSectionEquiv V n
      (HolomorphicPullback.pullback (Opens.inclusion h) (contMDiff_inclusion (I := 𝓘(ℂ, E)) h) n a) =
      Restrictions.holomorphicSectionRestrict h (holomorphicFormSectionEquiv U n a) := by
  change FunctionPure.holomorphicPureSectionEquiv V n
    (CoefficientMem.formToHolomorphicCoefficients V n
      (HolomorphicPullback.pullback (Opens.inclusion h) (contMDiff_inclusion (I := 𝓘(ℂ, E)) h) n a)) = _
  rw [CoefficientRestriction.formToHolomorphicCoefficients_pullback]
  rfl

def openDomainHolomorphicPresheafIso (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E] (n : ℕ) :
    (Holomorphic.Presheaf.presheafComplex E E).X n ≅ SectionSheaf.holomorphicSectionPresheaf E (Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule E n 0) :=
  NatIso.ofComponents (fun U => (holomorphicFormSectionEquiv U.unop n).toModuleIso) (by
    intro U V h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact holomorphicFormSectionEquiv_restrict (leOfHom h.unop) n a)

theorem openDomainHolomorphicPresheaf_isSheaf (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E] (n : ℕ) :
    TopCat.Presheaf.IsSheaf (X := TopCat.of E) ((Holomorphic.Presheaf.presheafComplex E E).X n) :=
  TopCat.Presheaf.isSheaf_of_iso (openDomainHolomorphicPresheafIso E n).symm
    (SectionSheaf.holomorphicSectionPresheaf_isSheaf E (Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule E n 0))

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.OpenDomainSheaf
