import OAI.RepresentationTheory.Weil.AdelicSplitting.TensorSpace

/-! # Special Linear Field Equiv -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.SpecialLinearFieldEquiv.CM

/-! Exact coefficient-field transport of special-linear matrices. -/

open scoped Classical _root_.Matrix
open _root_.Matrix
variable {I R S : Type*} [Fintype I] [DecidableEq I] [CommRing R] [CommRing S]

def map (e : R ≃+* S) : Matrix.SpecialLinearGroup I R ≃* Matrix.SpecialLinearGroup I S where
  toFun := Matrix.SpecialLinearGroup.map e.toRingHom
  invFun := Matrix.SpecialLinearGroup.map e.symm.toRingHom
  left_inv g := by
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    exact e.symm_apply_apply (g.val i j)
  right_inv g := by
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    exact e.apply_symm_apply (g.val i j)
  map_mul' g h := (Matrix.SpecialLinearGroup.map e.toRingHom).map_mul g h

theorem map_val (e : R ≃+* S) (g : Matrix.SpecialLinearGroup I R) (i j : I) :
    (CM.map e g).val i j = e (g.val i j) := rfl

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.SpecialLinearFieldEquiv.CM

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.SpecialLinearFieldEquiv.CM.Topology

/-! Continuous field equivalences induce homeomorphisms of special-linear groups. -/

open scoped Classical _root_.Matrix
open _root_.Matrix
open _root_.Topology
variable {I R S : Type*} [Fintype I] [DecidableEq I] [CommRing R] [CommRing S]
  [TopologicalSpace R] [TopologicalSpace S]
  (e : R ≃+* S)

theorem map_continuous (he : Continuous e) : Continuous (CM.map (I := I) e) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact he.comp ((continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val))

def homeomorphism (he : Continuous e) (hei : Continuous e.symm) :
    Matrix.SpecialLinearGroup I R ≃ₜ Matrix.SpecialLinearGroup I S where
  toEquiv := (CM.map e).toEquiv
  continuous_toFun := map_continuous e he
  continuous_invFun := map_continuous e.symm hei

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.SpecialLinearFieldEquiv.CM.Topology

end

end OAI
