import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.UnitaryBasisCoordinates

/-! # Unitary Coordinate Topology -/

namespace OAI.RepresentationTheory.Theta.Adelic.UnitaryCoordinateTopology

noncomputable section

/-! Continuous unitary changes of scalar field and Hermitian basis,
including explicit continuity of the inverse maps. -/

open scoped Classical

open _root_.Matrix OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.UnitaryBasisCoordinates.CM OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary

section Field
variable {R S I : Type*} [CommRing R] [CommRing S] [StarRing R] [StarRing S]
variable [TopologicalSpace R] [TopologicalSpace S]
variable [Fintype I] [DecidableEq I]

theorem specialUnitaryFieldMap_continuous (f : R →+* S) (hs : ∀ x, f (star x) = star (f x))
    (hc : Continuous f) (H : Matrix I I R) : Continuous (AlgebraicGeometry.HodgeConjecture.ThetaCycle.UnitaryBasisCoordinates.CM.specialUnitaryFieldMap f hs H) := by
  have hm : Continuous (f.mapMatrix : Matrix I I R → Matrix I I S) := continuous_pi fun i => continuous_pi fun j =>
    hc.comp ((continuous_apply j).comp (continuous_apply i))
  exact ((hm.units_map _).comp continuous_subtype_val).subtype_mk _

omit [TopologicalSpace R] [TopologicalSpace S] in
theorem specialUnitaryFieldEquiv_inverse_unit (e : R ≃+* S)
    (hs : ∀ x, e (star x) = star (e x)) (H : Matrix I I R) (g : SpecialUnitary.SU (H.map e.toRingHom)) :
    ((AlgebraicGeometry.HodgeConjecture.ThetaCycle.UnitaryBasisCoordinates.CM.specialUnitaryFieldEquiv e hs H).symm g).val =
      Units.map e.symm.toRingHom.mapMatrix.toMonoidHom g.val := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  apply e.injective
  have h := congrArg (fun q : SpecialUnitary.SU (H.map e.toRingHom) => q.val.val i j)
    ((AlgebraicGeometry.HodgeConjecture.ThetaCycle.UnitaryBasisCoordinates.CM.specialUnitaryFieldEquiv e hs H).apply_symm_apply g)
  exact h.trans (e.apply_symm_apply (g.val.val i j)).symm

def specialUnitaryFieldContinuousEquiv (e : R ≃+* S)
    (hs : ∀ x, e (star x) = star (e x)) (hc : Continuous e) (hi : Continuous e.symm)
    (H : Matrix I I R) : SpecialUnitary.SU H ≃ₜ* SpecialUnitary.SU (H.map e.toRingHom) where
  toMulEquiv := AlgebraicGeometry.HodgeConjecture.ThetaCycle.UnitaryBasisCoordinates.CM.specialUnitaryFieldEquiv e hs H
  continuous_toFun := specialUnitaryFieldMap_continuous e.toRingHom hs hc H
  continuous_invFun := by
    have hm : Continuous (e.symm.toRingHom.mapMatrix : Matrix I I S → Matrix I I R) := continuous_pi fun i => continuous_pi fun j =>
      hi.comp ((continuous_apply j).comp (continuous_apply i))
    apply continuous_induced_rng.mpr
    exact ((hm.units_map _).comp continuous_subtype_val).congr
      (fun g => (specialUnitaryFieldEquiv_inverse_unit e hs H g).symm)

end Field

variable {I : Type*} [Fintype I] [DecidableEq I]
variable (H H₀ : Matrix I I ℂ) (B : (Matrix I I ℂ)ˣ)
variable (hB : B.val.conjTranspose * H * B.val = H₀)

theorem specialUnitaryBasisEquiv_inverse_unit (g : SpecialUnitary.SU H₀) :
    ((AlgebraicGeometry.HodgeConjecture.ThetaCycle.UnitaryBasisCoordinates.CM.specialUnitaryBasisEquiv H H₀ B hB).symm g).val = B * g.val * B⁻¹ := by
  let e := AlgebraicGeometry.HodgeConjecture.ThetaCycle.UnitaryBasisCoordinates.CM.specialUnitaryBasisEquiv H H₀ B hB
  have h := congrArg Subtype.val (e.apply_symm_apply g)
  change B⁻¹ * (e.symm g).val * B = g.val at h
  change (e.symm g).val = B * g.val * B⁻¹
  calc
    _ = B * (B⁻¹ * (e.symm g).val * B) * B⁻¹ := by group
    _ = _ := by rw [h]

def specialUnitaryBasisContinuousEquiv : SpecialUnitary.SU H ≃ₜ* SpecialUnitary.SU H₀ where
  toMulEquiv := AlgebraicGeometry.HodgeConjecture.ThetaCycle.UnitaryBasisCoordinates.CM.specialUnitaryBasisEquiv H H₀ B hB
  continuous_toFun :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  continuous_invFun := by
    apply continuous_induced_rng.mpr
    exact ((continuous_const.mul continuous_subtype_val).mul continuous_const).congr
      (fun g => (specialUnitaryBasisEquiv_inverse_unit H H₀ B hB g).symm)

end

end OAI.RepresentationTheory.Theta.Adelic.UnitaryCoordinateTopology
