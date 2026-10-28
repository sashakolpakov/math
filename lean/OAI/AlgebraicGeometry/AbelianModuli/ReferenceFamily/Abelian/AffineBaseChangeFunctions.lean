import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.CechUnitContraction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Tensor.UnitKernelBasis

/-! # Affine Base Change Functions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian

noncomputable section

section

/-! The actual abelian structure-sheaf model's degree-zero kernel is
generated uniquely by its transported unit on arbitrary coefficient tests. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Modules

theorem StructureCechModel.AbelianStructureCechModel.universal_unit_kernel_basis
    {S : Scheme.{0}} [IsAffine S] {g : ℕ} {A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (F : StructureCechModel.AbelianStructureCechModel A) {T : Scheme.{0}} (t : T ⟶ S) :
    letI := F.quasi
    Function.Bijective (Cech.UnitKernelBasis.CechModelUnit.baseChangeUnitKernelMap A.scheme.hom t F.opens F.covers F.comparison) := by
  let := F.quasi
  let : Algebra Γ(S, ⊤) Γ(T, ⊤) := t.appTop.hom.toAlgebra
  obtain ⟨s, v, hs, hv⟩ := F.unit_contraction
  rw [Cech.UnitTensorComparison.CechModelUnit.baseChangeUnitKernelMap_eq_tensor A.scheme.hom t F.opens F.covers F.comparison]
  exact Tensor.UnitKernelBasis.tensorUnitKernelMap_bijective_of_contraction (F.complex.d 0 1).hom F.unitMap
    F.differential_unitMap s v hs hv

end

/-! Global functions on every affine base change of an abelian family
over an affine noetherian base are exactly the base functions. No
reducedness is required of either base or test scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Modules

theorem StructureCechModel.AbelianStructureCechModel.baseChange_globalFunctions_isIso
    {S : Scheme.{0}} [IsAffine S] {g : ℕ} {A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (F : StructureCechModel.AbelianStructureCechModel A)
    {Y T : Scheme.{0}} [IsAffine T] (a : Y ⟶ A.scheme.left) (ρ : Y ⟶ T) (t : T ⟶ S)
    (hp : IsPullback a ρ A.scheme.hom t) : IsIso ρ.appTop := by
  let := F.quasi
  let : QuasiIso (Quotients.FiniteDescent.CechModelBaseChange.Construction.CechBaseChangeMap.modelMap a A.scheme.hom ρ t hp.w
      (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj A.scheme.left) F.opens F.comparison) := F.baseChange Y T a ρ t hp
  let e := Cech.UnitFunctionEquiv.CechModelUnit.baseChangeFunctionsEquiv a A.scheme.hom ρ t hp.w F.opens F.covers F.comparison
  let u := Cech.UnitKernelBasis.CechModelUnit.baseChangeUnitKernelMap A.scheme.hom t F.opens F.covers F.comparison
  have hu : Function.Bijective u := F.universal_unit_kernel_basis t
  have he : e ∘ u = (ρ.appTop : Γ(T, ⊤) → Γ(Y, ⊤)) := by
    funext r
    exact (Cech.UnitKernelBasis.CechModelUnit.baseChangeUnitKernelMap_functions a A.scheme.hom ρ t hp.w
      F.opens F.covers F.comparison r).trans (BaseStructureSections.baseStructureUnitMap_apply ρ r)
  apply (ConcreteCategory.isIso_iff_bijective ρ.appTop).mpr
  exact he ▸ e.bijective.comp hu

theorem AffineBaseChangeFunctions.abelian_affine_baseChange_globalFunctions_isIso
    {S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    {Y T : Scheme.{0}} [IsAffine T] (a : Y ⟶ A.scheme.left) (ρ : Y ⟶ T) (t : T ⟶ S)
    (hp : IsPullback a ρ A.scheme.hom t) : IsIso ρ.appTop := by
  obtain ⟨F⟩ := StructureCechModel.abelianStructureCechModel_nonempty A
  exact F.baseChange_globalFunctions_isIso a ρ t hp

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian
