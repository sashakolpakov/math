import OAI.RepresentationTheory.Weil.AdelicSplitting.UnitaryBase

/-! # Intrinsic Unitary Field Equiv -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicUnitaryFieldEquiv.Intrinsic

noncomputable section

/-! A star-preserving field presentation gives an actual equivalence of
the specified unitary groups, in both coordinate directions. -/

open scoped Classical _root_.Matrix

open OAI.RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction

variable {I R S : Type} [Fintype I] [DecidableEq I]
variable [CommRing R] [StarRing R] [CommRing S] [StarRing S]

theorem inverse_preserves_star (e : R ≃+* S) (he : ∀ x, e (star x) = star (e x))
    (y : S) : e.symm (star y) = star (e.symm y) := by
  apply e.injective
  rw [e.apply_symm_apply,he,e.apply_symm_apply]

omit [Fintype I] [DecidableEq I] [StarRing R] [StarRing S] in
theorem inverse_mapped_form (e : R ≃+* S) (H : Matrix I I R) :
    (H.map e.toRingHom).map e.symm.toRingHom = H := by
  ext i j
  exact e.symm_apply_apply _

def unitaryFieldInverse (e : R ≃+* S) (he : ∀ x, e (star x) = star (e x))
    (H : Matrix I I R) (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary (H.map e.toRingHom)) : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H :=
  ⟨Units.map e.symm.toRingHom.mapMatrix.toMonoidHom g.val,by
    have h := congrArg (fun M : Matrix I I S => M.map e.symm.toRingHom) g.property
    rw [Matrix.map_mul,Matrix.map_mul,Weil.AdelicSplitting.UnitaryBase.Construction.map_conjTranspose e.symm.toRingHom
      (inverse_preserves_star e he),inverse_mapped_form] at h
    exact h⟩

def unitaryFieldEquiv (e : R ≃+* S) (he : ∀ x, e (star x) = star (e x))
    (H : Matrix I I R) : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H ≃* Weil.AdelicSplitting.UnitaryBase.Construction.Unitary (H.map e.toRingHom) where
  toFun := Weil.AdelicSplitting.UnitaryBase.Construction.unitaryBaseChange e.toRingHom he H
  invFun := unitaryFieldInverse e he H
  left_inv g := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    exact e.symm_apply_apply _
  right_inv g := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    exact e.apply_symm_apply _
  map_mul' := (Weil.AdelicSplitting.UnitaryBase.Construction.unitaryBaseChange e.toRingHom he H).map_mul

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicUnitaryFieldEquiv.Intrinsic
