import OAI.AlgebraicGeometry.Quotients.FiniteDescent.FiberScalar
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.FieldPoint
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.FieldTensor
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ScalarFunctor
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ShortComplexFirstCycles

/-! # Residue Model -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ResidueModel

noncomputable section

/-! Support of the model's dual cokernel supplies a nonzero cycle in
the tensor over the local ring and its residue field. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

universe u

namespace Construction.ResidueModelCycles

def firstCyclesIso {R : Type u} [CommRing R] {C D : ShortComplex (ModuleCat.{u} R)} (e : C ≅ D) :
    C.f.hom.ker ≃ₗ[R] D.f.hom.ker :=
  LinearEquiv.ofLinearMap (ShortComplexFirstCycles.Construction.LocalSectionLifting.shortComplexFirstCyclesMap e.hom)
    (ShortComplexFirstCycles.Construction.LocalSectionLifting.shortComplexFirstCyclesMap e.inv)
    (by rw [← ShortComplexFirstCycles.Construction.LocalSectionLifting.shortComplexFirstCyclesMap_comp, e.inv_hom_id,
      ShortComplexFirstCycles.Construction.LocalSectionLifting.shortComplexFirstCyclesMap_id])
    (by rw [← ShortComplexFirstCycles.Construction.LocalSectionLifting.shortComplexFirstCyclesMap_comp, e.hom_inv_id,
      ShortComplexFirstCycles.Construction.LocalSectionLifting.shortComplexFirstCyclesMap_id])

theorem evaluation_kernel (S : Scheme.{u}) (x : S) :
    (S.toSpecΓ x).asIdeal = RingHom.ker (S.Γevaluation x).hom := by
  have ht := FieldPoint.Construction.FieldPointPrime.kernel (S.fromSpecResidueField x) (default : Spec (S.residueField x))
  have ht' : (S.toSpecΓ x).asIdeal = RingHom.ker (S.fromSpecResidueField x).appTop.hom :=
    (congrArg (fun y : S => (S.toSpecΓ y).asIdeal)
      (S.fromSpecResidueField_apply x (default : Spec (S.residueField x)))).symm.trans ht
  have he : (S.Γevaluation x).hom = (Scheme.ΓSpecIso (S.residueField x)).hom.hom.comp
      (S.fromSpecResidueField x).appTop.hom :=
    (congrArg (fun a : Γ(S, ⊤) ⟶ S.residueField x => a.hom)
      (FiberScalar.Construction.FiberScalarMaps.fromResidue_appTop S x)).symm
  rw [he, RingHom.ker_comp_of_injective _ (Scheme.ΓSpecIso (S.residueField x)).commRingCatIsoToRingEquiv.injective]
  exact ht'

theorem exists_cycle (S : Scheme.{u}) (x : S) (C : ShortComplex (ModuleCat.{u} Γ(S, ⊤)))
    [Module.Finite Γ(S, ⊤) C.X₁] [Module.Projective Γ(S, ⊤) C.X₁]
    [Module.Finite Γ(S, ⊤) C.X₂] [Module.Projective Γ(S, ⊤) C.X₂]
    (hs : S.toSpecΓ x ∈ Module.support Γ(S, ⊤) (KernelSupportIs.Construction.KernelSupport.dualCokernel C.f.hom)) :
    letI : Algebra Γ(S, ⊤) (S.presheaf.stalk x) := (S.presheaf.germ ⊤ x trivial).hom.toAlgebra
    ∃ z : IsLocalRing.ResidueField (S.presheaf.stalk x) ⊗[S.presheaf.stalk x]
      ((S.presheaf.stalk x) ⊗[Γ(S, ⊤)] C.X₁),
      (C.f.hom.baseChange (S.presheaf.stalk x)).baseChange
        (IsLocalRing.ResidueField (S.presheaf.stalk x)) z = 0 ∧ z ≠ 0 := by
  let R := Γ(S, ⊤)
  let A := S.presheaf.stalk x
  let K := IsLocalRing.ResidueField A
  let f : R →+* A := (S.presheaf.germ ⊤ x trivial).hom
  let g : A →+* K := (S.residue x).hom
  let : Algebra R A := f.toAlgebra
  let : Algebra R K := (S.Γevaluation x).hom.toAlgebra
  have hn : Nontrivial (C.f.hom.baseChange K).ker :=
    (KernelSupportIs.Construction.KernelSupport.field_kernel_iff K C.f.hom).mpr
      ((FieldTensor.Construction.FieldTensorSupport.nontrivial_iff K (KernelSupportIs.Construction.KernelSupport.dualCokernel C.f.hom)
        (S.toSpecΓ x) (evaluation_kernel S x)).mpr hs)
  let F := ModuleBaseChangeComplex.Construction.LocalSectionLifting.moduleBaseChangeFunctor R A
  let G := ModuleCat.extendScalars g
  let e : ModuleCat.extendScalars (S.Γevaluation x).hom ≅ F ⋙ G :=
    ModuleCat.extendScalarsComp f g ≪≫
      Functor.isoWhiskerRight (ScalarFunctor.Construction.ScalarFunctorComparison.iso R A).symm G
  have hn' : Nontrivial (C.map (ModuleCat.extendScalars (S.Γevaluation x).hom)).f.hom.ker := hn
  have ht : Nontrivial (C.map (F ⋙ G)).f.hom.ker := (firstCyclesIso (C.mapNatIso e)).nontrivial_congr.mp hn'
  obtain ⟨z, hz⟩ := exists_ne (0 : (C.map (F ⋙ G)).f.hom.ker)
  refine ⟨z.val, z.property, ?_⟩
  intro hzero
  exact hz (Subtype.ext hzero)

end Construction.ResidueModelCycles

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ResidueModel
