import OAI.AlgebraicGeometry.FormalGeometry.Completion.SmoothToNormalization
import OAI.AlgebraicGeometry.FormalGeometry.Completion.GraphUnramified

/-! # Unramified Normalization -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.UnramifiedNormalization.Construction

noncomputable section

/-! # Completion: the integral normalization factor is formally unramified -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

/-- The diagonal of the actual integral normalization factor is an open immersion. -/
theorem proper_smooth_fromNormalization_diagonal_isOpenImmersion
    (K : Type u) [Field K] {X Y : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of K)) [IsProper p] [Smooth p] [ConnectedSpace X]
    (f : X ⟶ Y) [IsProper f] [Smooth f] :
    IsOpenImmersion (pullback.diagonal f.fromNormalization) := by
  have : Smooth f.toNormalization := SmoothToNormalization.Construction.proper_smooth_toNormalization_smooth K p f
  have : Surjective f.toNormalization := Proper.Normalization.Construction.proper_toNormalization_surjective f
  have : IsProper f.toNormalization := Proper.Normalization.Construction.proper_toNormalization f
  have : IsOpenImmersion (SmoothToNormalization.Construction.normalizationGraph f) :=
    SmoothToNormalization.Construction.proper_smooth_normalizationGraph_isOpenImmersion K p f
  let e : pullback f.fromNormalization f ≅
      pullback (f.toNormalization ≫ f.fromNormalization) f.fromNormalization :=
    pullbackSymmetry _ _ ≪≫ pullback.congrHom (by simp) rfl
  have he : (pullback.lift (𝟙 X) f.toNormalization (by simp) :
      X ⟶ pullback (f.toNormalization ≫ f.fromNormalization) f.fromNormalization) =
      SmoothToNormalization.Construction.normalizationGraph f ≫ e.hom := by
    apply pullback.hom_ext <;> simp [SmoothToNormalization.Construction.normalizationGraph, e]
  have : IsOpenImmersion (pullback.lift (𝟙 X) f.toNormalization (by simp) :
      X ⟶ pullback (f.toNormalization ≫ f.fromNormalization) f.fromNormalization) := by
    rw [he]
    infer_instance
  exact GraphUnramified.Construction.diagonal_isOpenImmersion_of_open_graph f.toNormalization f.fromNormalization

/-- The actual integral factor of this proper smooth family is formally unramified. -/
theorem proper_smooth_fromNormalization_formallyUnramified
    (K : Type u) [Field K] {X Y : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of K)) [IsProper p] [Smooth p] [ConnectedSpace X]
    (f : X ⟶ Y) [IsProper f] [Smooth f] : FormallyUnramified f.fromNormalization := by
  have := proper_smooth_fromNormalization_diagonal_isOpenImmersion K p f
  infer_instance

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.UnramifiedNormalization.Construction
