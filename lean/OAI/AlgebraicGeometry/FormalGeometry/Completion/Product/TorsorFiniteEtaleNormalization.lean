import OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.TorsorIntegralComponent
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.SmoothFiniteEtaleNormalization

/-! # Torsor Finite Etale Normalization -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.TorsorFiniteEtaleNormalization.Construction

noncomputable section

/-! # Completion: finite étale normalization for the actual product torsor -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

/-- The normalization factor of the entire actual finite-coefficient product torsor is finite étale. -/
theorem productTorsor_fromNormalization_finite_etale {K : Type u} [Field K]
    {A B : Scheme.{u}} [IsIntegral B]
    (p : A ⟶ Spec (CommRingCat.of K)) [IsProper p] [Smooth p]
    (q : B ⟶ Spec (CommRingCat.of K)) [IsProper q] [Smooth q]
    {ℓ n : ℕ} [NeZero (ℓ ^ n)] (E : FiniteTorsor.App.Construction.FiniteCoefficientExtension ℓ n (pullback p q)) :
    IsFinite (TorsorNormalization.Construction.productTorsorToFactor p q E).fromNormalization ∧
      Etale (TorsorNormalization.Construction.productTorsorToFactor p q E).fromNormalization := by
  have : Etale E.gluedSchemeToBase := E.gluedSchemeToBase_etale
  have : Smooth (TorsorNormalization.Construction.productTorsorToFactor p q E) := by unfold TorsorNormalization.Construction.productTorsorToFactor; infer_instance
  exact Proper.SmoothFiniteEtaleNormalization.Construction.proper_smooth_family_normalization_finite_etale K
    (TorsorNormalization.Construction.productTorsorToFactor p q E ≫ q) q (TorsorNormalization.Construction.productTorsorToFactor p q E)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.TorsorFiniteEtaleNormalization.Construction
