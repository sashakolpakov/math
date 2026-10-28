import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CochainZero
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Cochain Base Change Cycles -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.CochainBaseChangeCycles.Construction

noncomputable section

/-! Canonical base change of degree-zero cochain cycles. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped ChangeOfRings

universe u

variable {R A : Type u} [CommRing R] [CommRing A] (r : R →+* A)

abbrev cochainExtendScalars (C : CochainComplex (ModuleCat.{u} R) ℕ) :=
  ((ModuleCat.extendScalars r).mapHomologicalComplex (ComplexShape.up ℕ)).obj C

def cochainBaseChangeFirstCycle (C : CochainComplex (ModuleCat.{u} R) ℕ)
    (x : (C.d 0 1).hom.ker) : ((cochainExtendScalars r C).d 0 1).hom.ker :=
  ⟨(1 : A) ⊗ₜ[R,r] x.val, by
    change (ModuleCat.extendScalars r).map (C.d 0 1) ((1 : A) ⊗ₜ[R,r] x.val) = 0
    rw [ModuleCat.ExtendScalars.map_tmul]
    have hx : C.d 0 1 x.val = 0 := x.property
    rw [hx, TensorProduct.tmul_zero]
    rfl⟩

theorem cochainBaseChangeFirstCycle_naturality
    {C D : CochainComplex (ModuleCat.{u} R) ℕ} (φ : C ⟶ D)
    [QuasiIsoAt φ 0]
    [QuasiIsoAt (((ModuleCat.extendScalars r).mapHomologicalComplex
      (ComplexShape.up ℕ)).map φ) 0]
    (x : (C.d 0 1).hom.ker) :
    AlgebraicGeometry.Quotients.FiniteDescent.CochainZero.Construction.CochainZeroCycles.kernelEquiv
        (((ModuleCat.extendScalars r).mapHomologicalComplex (ComplexShape.up ℕ)).map φ)
        (cochainBaseChangeFirstCycle r C x) =
      cochainBaseChangeFirstCycle r D (AlgebraicGeometry.Quotients.FiniteDescent.CochainZero.Construction.CochainZeroCycles.kernelEquiv φ x) := by
  apply Subtype.ext
  rw [AlgebraicGeometry.Quotients.FiniteDescent.CochainZero.Construction.CochainZeroCycles.kernelEquiv_apply_val]
  change (ModuleCat.extendScalars r).map (φ.f 0) ((1 : A) ⊗ₜ[R,r] x.val) =
    (1 : A) ⊗ₜ[R,r] (AlgebraicGeometry.Quotients.FiniteDescent.CochainZero.Construction.CochainZeroCycles.kernelEquiv φ x).val
  rw [ModuleCat.ExtendScalars.map_tmul, AlgebraicGeometry.Quotients.FiniteDescent.CochainZero.Construction.CochainZeroCycles.kernelEquiv_apply_val]

theorem cochain_cycle_lifting_iff_of_universal_quasiIso
    {C D : CochainComplex (ModuleCat.{u} R) ℕ} (φ : C ⟶ D)
    [QuasiIsoAt φ 0]
    [QuasiIsoAt (((ModuleCat.extendScalars r).mapHomologicalComplex
      (ComplexShape.up ℕ)).map φ) 0] :
    Function.Surjective (cochainBaseChangeFirstCycle r C) ↔
      Function.Surjective (cochainBaseChangeFirstCycle r D) := by
  let e := AlgebraicGeometry.Quotients.FiniteDescent.CochainZero.Construction.CochainZeroCycles.kernelEquiv φ
  let eA := AlgebraicGeometry.Quotients.FiniteDescent.CochainZero.Construction.CochainZeroCycles.kernelEquiv
    (((ModuleCat.extendScalars r).mapHomologicalComplex (ComplexShape.up ℕ)).map φ)
  constructor
  · intro h z
    obtain ⟨x, hx⟩ := h (eA.symm z)
    refine ⟨e x, ?_⟩
    rw [← cochainBaseChangeFirstCycle_naturality r φ, hx, LinearEquiv.apply_symm_apply]
  · intro h z
    obtain ⟨x, hx⟩ := h (eA z)
    refine ⟨e.symm x, eA.injective ?_⟩
    rw [cochainBaseChangeFirstCycle_naturality r φ, LinearEquiv.apply_symm_apply]
    exact hx

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.CochainBaseChangeCycles.Construction
