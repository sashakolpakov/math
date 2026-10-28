import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ScalarRingTensorEquiv

/-! # Scalar Ring Cycle Equiv -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ScalarRingCycleEquiv.Construction

noncomputable section

/-! The cycle-lifting condition is invariant under compatible isomorphisms of coefficient rings. -/

open _root_.CategoryTheory
open scoped ChangeOfRings

universe u

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
variable (r : R →+* A) (s : R →+* B) (e : A ≃+* B) (h : ∀ x, e (r x) = s x)
variable (C : CochainComplex (ModuleCat.{u} R) ℕ)

def scalarRingCochainFirstCyclesEquiv :
    ((CochainBaseChangeCycles.Construction.cochainExtendScalars r C).d 0 1).hom.ker ≃+
      ((CochainBaseChangeCycles.Construction.cochainExtendScalars s C).d 0 1).hom.ker := by
  let e₀ := ScalarRingTensorEquiv.Construction.scalarRingTensorAddEquiv r s e h (C.X 0)
  let e₁ := ScalarRingTensorEquiv.Construction.scalarRingTensorAddEquiv r s e h (C.X 1)
  refine
    { toFun := fun x ↦ ⟨e₀ x.val, ?_⟩
      invFun := fun y ↦ ⟨e₀.symm y.val, ?_⟩
      left_inv := fun x ↦ Subtype.ext (e₀.symm_apply_apply x.val)
      right_inv := fun y ↦ Subtype.ext (e₀.apply_symm_apply y.val)
      map_add' := fun x y ↦ Subtype.ext (map_add e₀ x.val y.val) }
  · exact (ScalarRingTensorEquiv.Construction.scalarRingTensorAddEquiv_naturality r s e h (C.d 0 1) x.val).symm.trans
      ((congrArg e₁ x.property).trans (map_zero e₁))
  · apply e₁.injective
    have hn := ScalarRingTensorEquiv.Construction.scalarRingTensorAddEquiv_naturality r s e h (C.d 0 1) (e₀.symm y.val)
    exact (hn.trans (congrArg (fun z ↦ (CochainBaseChangeCycles.Construction.cochainExtendScalars s C).d 0 1 z)
      (e₀.apply_symm_apply y.val))).trans (y.property.trans (map_zero e₁).symm)

theorem scalarRingCochainFirstCyclesEquiv_unit (x : (C.d 0 1).hom.ker) :
    scalarRingCochainFirstCyclesEquiv r s e h C (CochainBaseChangeCycles.Construction.cochainBaseChangeFirstCycle r C x) =
      CochainBaseChangeCycles.Construction.cochainBaseChangeFirstCycle s C x := by
  apply Subtype.ext
  change ScalarRingTensorEquiv.Construction.scalarRingTensorAddEquiv r s e h (C.X 0) ((1 : A) ⊗ₜ[R,r] x.val) =
    (1 : B) ⊗ₜ[R,s] x.val
  rw [ScalarRingTensorEquiv.Construction.scalarRingTensorAddEquiv_tmul, e.map_one]

include e h in
theorem cochain_cycles_lift_iff_of_scalarRingIso :
    Function.Surjective (CochainBaseChangeCycles.Construction.cochainBaseChangeFirstCycle r C) ↔
      Function.Surjective (CochainBaseChangeCycles.Construction.cochainBaseChangeFirstCycle s C) := by
  let E := scalarRingCochainFirstCyclesEquiv r s e h C
  constructor
  · intro hr z
    obtain ⟨x, hx⟩ := hr (E.symm z)
    refine ⟨x, ?_⟩
    exact (scalarRingCochainFirstCyclesEquiv_unit r s e h C x).symm.trans
      ((congrArg E hx).trans (E.apply_symm_apply z))
  · intro hs z
    obtain ⟨x, hx⟩ := hs (E z)
    exact ⟨x, E.injective ((scalarRingCochainFirstCyclesEquiv_unit r s e h C x).trans hx)⟩

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ScalarRingCycleEquiv.Construction
