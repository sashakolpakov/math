import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AffineProduct.TransitionDerivation
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AffineProduct.AutomorphismLaws
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TransitionDerivationFaithfulness

/-! # Derivation Laws -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AffineProduct.DerivationLaws

noncomputable section

/-! Scheme transition composition becomes addition of derivations.
The coefficient is zero exactly for the identity scheme automorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (k : Type) [Field k] (X : Over (Spec (.of k))) [IsAffine X.left]

theorem affineProductTransitionDerivation_congr
    (e f : (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).obj X ≅ (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).obj X)
    (he : (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).map e.hom = 𝟙 _)
    (hf : (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).map f.hom = 𝟙 _) (h : e = f) :
    TransitionDerivation.affineProductTransitionDerivation k X e he = TransitionDerivation.affineProductTransitionDerivation k X f hf := by
  subst f
  rfl

theorem affineProductTransitionDerivation_trans
    (e f : (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).obj X ≅ (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).obj X)
    (he : (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).map e.hom = 𝟙 _)
    (hf : (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).map f.hom = 𝟙 _)
    (hef : (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).map (e ≪≫ f).hom = 𝟙 _) :
    TransitionDerivation.affineProductTransitionDerivation k X (e ≪≫ f) hef =
      TransitionDerivation.affineProductTransitionDerivation k X e he + TransitionDerivation.affineProductTransitionDerivation k X f hf := by
  unfold TransitionDerivation.affineProductTransitionDerivation
  have ht := Dual.TransitionDerivationLaws.dualTensorTransitionDerivation_trans
    (Coordinates.affineProductAutomorphismAlgebra k X f) (Coordinates.affineProductAutomorphismAlgebra k X e)
    (ReductionIdentity.affineProductAutomorphismAlgebra_reduction k X f hf)
    (ReductionIdentity.affineProductAutomorphismAlgebra_reduction k X e he)
  exact (Dual.TransitionDerivationFaithfulness.dualTensorTransitionDerivation_congr _ _ _ _
    (AutomorphismLaws.affineProductAutomorphismAlgebra_trans k X e f)).trans (ht.trans (add_comm _ _))

theorem affineProductTransitionDerivation_refl :
    TransitionDerivation.affineProductTransitionDerivation k X (Iso.refl _)
      ((Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).map_id _) = 0 := by
  unfold TransitionDerivation.affineProductTransitionDerivation
  exact (Dual.TransitionDerivationFaithfulness.dualTensorTransitionDerivation_congr _ _ _ _
    (AutomorphismLaws.affineProductAutomorphismAlgebra_refl k X)).trans Dual.TransitionDerivationFaithfulness.dualTensorTransitionDerivation_refl

theorem affineProductTransitionDerivation_faithful
    (e f : (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).obj X ≅ (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).obj X)
    (he : (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).map e.hom = 𝟙 _)
    (hf : (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).map f.hom = 𝟙 _)
    (h : TransitionDerivation.affineProductTransitionDerivation k X e he = TransitionDerivation.affineProductTransitionDerivation k X f hf) : e = f := by
  apply AutomorphismLaws.affineProductAutomorphismAlgebra_injective k X
  exact Dual.TransitionDerivationFaithfulness.dualTensorTransitionDerivation_faithful
    (Coordinates.affineProductAutomorphismAlgebra k X e) (Coordinates.affineProductAutomorphismAlgebra k X f)
    (ReductionIdentity.affineProductAutomorphismAlgebra_reduction k X e he)
    (ReductionIdentity.affineProductAutomorphismAlgebra_reduction k X f hf) h

theorem affineProductTransitionDerivation_eq_zero_iff
    (e : (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).obj X ≅ (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).obj X)
    (he : (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).map e.hom = 𝟙 _) :
    TransitionDerivation.affineProductTransitionDerivation k X e he = 0 ↔ e = Iso.refl _ := by
  constructor
  · intro h
    exact affineProductTransitionDerivation_faithful k X e (Iso.refl _) he
      ((Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).map_id _)
      (h.trans (affineProductTransitionDerivation_refl k X).symm)
  · rintro rfl
    exact affineProductTransitionDerivation_refl k X

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AffineProduct.DerivationLaws
