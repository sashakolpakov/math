import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.CoefficientUnitExactness
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CohomologySectionLifting

/-! # Unit Cycle Lifting -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The actual unit of an abelian structure-sheaf model lifts every
degree-zero residue cycle, including over nonreduced local bases. Consequently
the first differential of a local minimal structure-sheaf model vanishes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct

universe u

theorem Residue.UnitCycleLifting.residue_cycle_lift_of_unit
    {R M N : Type u} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (d : M →ₗ[R] N) (v : R →ₗ[R] M) (hv : d.comp v = 0)
    (hex : (d.lTensor (IsLocalRing.ResidueField R)).ker =
      (v.lTensor (IsLocalRing.ResidueField R)).range)
    (z : IsLocalRing.ResidueField R ⊗[R] M)
    (hz : d.baseChange (IsLocalRing.ResidueField R) z = 0) :
    ∃ x : M, d x = 0 ∧ (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] x = z := by
  have hz' : z ∈ (v.lTensor (IsLocalRing.ResidueField R)).range := by
    rw [← hex]
    exact hz
  obtain ⟨w, hw⟩ := hz'
  let e := TensorProduct.AlgebraTensorModule.rid R (IsLocalRing.ResidueField R)
    (IsLocalRing.ResidueField R)
  obtain ⟨r, hr⟩ := IsLocalRing.residue_surjective (e w)
  refine ⟨v r, LinearMap.congr_fun hv r, ?_⟩
  have hw' : w = (algebraMap R (IsLocalRing.ResidueField R) r) ⊗ₜ[R] (1 : R) := by
    rw [← e.symm_apply_apply w, ← hr]
    rfl
  rw [hw', LinearMap.lTensor_tmul] at hw
  rw [show v r = r • v 1 by simpa using v.map_smul r (1 : R)]
  simpa only [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul,
    TensorProduct.tmul_smul] using hw

variable {S : Scheme.{u}} [IsAffine S] [IsLocalRing Γ(S, ⊤)]
variable {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S)
variable {I : Type u} [LinearOrder I] (U : I → A.scheme.left.Opens) (hU : iSup U = ⊤)
variable {D : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
variable (φ : D ⟶ SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex A.scheme.hom (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj A.scheme.left) U)
variable [QuasiIsoAt φ 0]
variable [QuasiIsoAt (Quotients.FiniteDescent.CechModelBaseChange.Construction.CechBaseChangeMap.modelMap
  (CategoryTheory.Limits.pullback.fst A.scheme.hom
    (ReferenceFamily.Affine.CoefficientUnitExactness.coefficientFieldPoint S (IsLocalRing.ResidueField Γ(S, ⊤)))) A.scheme.hom
  (CategoryTheory.Limits.pullback.snd A.scheme.hom
    (ReferenceFamily.Affine.CoefficientUnitExactness.coefficientFieldPoint S (IsLocalRing.ResidueField Γ(S, ⊤))))
  (ReferenceFamily.Affine.CoefficientUnitExactness.coefficientFieldPoint S (IsLocalRing.ResidueField Γ(S, ⊤)))
  CategoryTheory.Limits.pullback.condition (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj A.scheme.left) U φ) 0]

include A U hU φ

theorem Abelian.Schemes.AbelianScheme.structureModel_residue_cycle_lift
    (z : IsLocalRing.ResidueField Γ(S, ⊤) ⊗[Γ(S, ⊤)] D.X 0)
    (hz : (D.d 0 1).hom.baseChange (IsLocalRing.ResidueField Γ(S, ⊤)) z = 0) :
    ∃ x : D.X 0, D.d 0 1 x = 0 ∧
      (1 : IsLocalRing.ResidueField Γ(S, ⊤)) ⊗ₜ[Γ(S, ⊤)] x = z :=
  Residue.UnitCycleLifting.residue_cycle_lift_of_unit (D.d 0 1).hom (ReferenceFamily.Cech.ModelUnit.CechModelUnit.unitMap A.scheme.hom U hU φ)
    (ReferenceFamily.Cech.ModelUnit.CechModelUnit.differential_unitMap A.scheme.hom U hU φ)
    (ReferenceFamily.Affine.CoefficientUnitExactness.abelianCoefficient_unit_exactness A (IsLocalRing.ResidueField Γ(S, ⊤)) U hU φ).2 z hz

theorem Abelian.Schemes.AbelianScheme.structureModel_minimal_first_zero
    (P : Quotients.FiniteDescent.LocalMinimalShort.Construction.LocalSectionLifting.LocalMinimalShortComplex (D.sc' 0 1 2)) :
    P.complex.f.hom = 0 :=
  P.first_zero_of_residue_cycles_lift (A.structureModel_residue_cycle_lift U hU φ)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
