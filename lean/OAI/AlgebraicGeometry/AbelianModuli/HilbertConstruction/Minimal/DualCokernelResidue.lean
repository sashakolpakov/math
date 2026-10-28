import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RankOneDualPresentation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Minimal.FirstDifferentialIdeal
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ShortComplexLastCokernel
import Mathlib.Algebra.Category.ModuleCat.Kernels

/-! # Dual Cokernel Residue -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The actual last cokernel of the dual minimal short complex is the residue module when its first source has rank one and its coefficients generate the maximal ideal. Endpoint-controlled homotopies transfer this to the original model. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits IsLocalRing
universe u

def Minimal.DualCokernelResidue.rankOneDualEquiv {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (e : R ≃ₗ[R] M) : Module.Dual R M ≃ₗ[R] R where
  toFun ℓ := ℓ (e 1)
  invFun r := r • e.symm.toLinearMap
  left_inv ℓ := by
    apply LinearMap.ext
    intro x
    obtain ⟨r, rfl⟩ := e.surjective x
    have he : e r = r • e 1 := by
      simpa only [smul_eq_mul, mul_one] using e.map_smul r (1 : R)
    change ℓ (e 1) * e.symm (e r) = ℓ (e r)
    rw [e.symm_apply_apply, he, ℓ.map_smul, smul_eq_mul, mul_comm]
  right_inv r := by
    change r * e.symm (e 1) = r
    rw [e.symm_apply_apply, mul_one]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {R : Type u} [CommRing R] [IsLocalRing R]

def Local.MinimalShortComplex.LocalSectionLifting.LocalMinimalShortComplex.dualCokernelResidueIso
    {S : ShortComplex (ModuleCat.{u} R)} (Q : Local.MinimalShortComplex.LocalSectionLifting.LocalMinimalShortComplex S)
    (e : R ≃ₗ[R] Q.complex.X₁) (hI : Q.firstDifferentialIdeal = maximalIdeal R) :
    cokernel (HilbertConstruction.Module.DualFunctor.dualModuleShortComplex Q.complex).g ≅ ModuleCat.of R (ResidueField R) := by
  let c := Module.Free.chooseBasis R Q.complex.X₂
  let E := Minimal.DualCokernelResidue.rankOneDualEquiv e
  have hmap : Q.complex.f.hom.dualMap.range.map E.toLinearMap = maximalIdeal R := by
    rw [← LinearMap.range_comp]
    change (RankOneDualPresentation.rankOneDualCoefficientMap e Q.complex.f.hom).range = maximalIdeal R
    exact (RankOneDualPresentation.rankOneDualCoefficientMap_range c e Q.complex.f.hom).trans
      ((RankOneDifferentialCoefficients.differentialCoefficientIdeal_of_rank_one_source
        (Module.Free.chooseBasis R Q.complex.X₁) c Q.complex.f.hom e).symm.trans hI)
  let eQ : (Module.Dual R Q.complex.X₁ ⧸ Q.complex.f.hom.dualMap.range) ≃ₗ[R] ResidueField R :=
    Submodule.Quotient.equiv Q.complex.f.hom.dualMap.range (maximalIdeal R) E hmap
  exact ModuleCat.cokernelIsoRangeQuotient (HilbertConstruction.Module.DualFunctor.dualModuleShortComplex Q.complex).g ≪≫ eQ.toModuleIso

def Local.MinimalShortComplex.LocalSectionLifting.LocalMinimalShortComplex.originalDualCokernelResidueIso
    {S : ShortComplex (ModuleCat.{u} R)} (Q : Local.MinimalShortComplex.LocalSectionLifting.LocalMinimalShortComplex S)
    (e : R ≃ₗ[R] Q.complex.X₁) (hI : Q.firstDifferentialIdeal = maximalIdeal R) :
    cokernel (HilbertConstruction.Module.DualFunctor.dualModuleShortComplex S).g ≅ ModuleCat.of R (ResidueField R) :=
  ShortComplexLastCokernel.dualShortComplexLastCokernelIso Q.equivalence Q.hom_h₀ Q.inv_h₀ ≪≫
    Q.dualCokernelResidueIso e hI

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
