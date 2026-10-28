import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Tensor.SpecialFiberCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ReductionFixedMorphisms

/-! # Automorphism Fiber Identity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Tensor.AutomorphismFiberIdentity

noncomputable section

/-! Preserving the literal tensor reduction makes the induced scheme
automorphism the identity on its actual special fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable (k A : Type) [Field k] [CommRing A] [Algebra k A]

local instance tensorAutomorphismFiberIdentity_commRing : CommRing (DualNumber k ⊗[k] A) :=
  Algebra.TensorProduct.instCommRing (R := k) (A := DualNumber k) (B := A)

theorem tensorAlgebraAutomorphism_fiberIdentity
    (e : (DualNumber k ⊗[k] A) ≃ₐ[DualNumber k] (DualNumber k ⊗[k] A))
    (he : ∀ u, Dual.TensorReduction.dualTensorReduction k A (e u) = Dual.TensorReduction.dualTensorReduction k A u) :
    (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).map (EtaleSplittingAt.EtaleSplitting.affineAlgIso (DualNumber k) (DualNumber k ⊗[k] A) e).hom =
      𝟙 _ := by
  have hq : Spec.map (CommRingCat.ofHom (Dual.TensorReduction.dualTensorReduction k A).toRingHom) ≫
      Spec.map (CommRingCat.ofHom e.toRingHom) = Spec.map (CommRingCat.ofHom (Dual.TensorReduction.dualTensorReduction k A).toRingHom) := by
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact RingHom.ext he
  let b := SpecialFiberCoordinates.dualTensorSpecialFiberIso k A
  have : IsIso b.hom.left := (Over.forget _).map_isIso b.hom
  apply (Dual.ReductionFixedMorphisms.dualReduction_map_identity_iff k (EtaleSplittingAt.EtaleSplitting.affineAlgIso (DualNumber k) (DualNumber k ⊗[k] A) e).hom).mpr
  apply (cancel_epi b.hom.left).mp
  change b.hom.left ≫ (VaryingDualReduction.dualFamilyReduction k (EtaleSplittingAt.EtaleSplitting.affineOver (DualNumber k) (DualNumber k ⊗[k] A)) ≫
    Spec.map (CommRingCat.ofHom e.toRingHom)) =
      b.hom.left ≫ VaryingDualReduction.dualFamilyReduction k (EtaleSplittingAt.EtaleSplitting.affineOver (DualNumber k) (DualNumber k ⊗[k] A))
  rw [← Category.assoc]
  change ((SpecialFiberCoordinates.dualTensorSpecialFiberIso k A).hom.left ≫ _) ≫ _ = (SpecialFiberCoordinates.dualTensorSpecialFiberIso k A).hom.left ≫ _
  rw [SpecialFiberCoordinates.dualTensorSpecialFiberIso_hom_reduction]
  exact hq

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Tensor.AutomorphismFiberIdentity
