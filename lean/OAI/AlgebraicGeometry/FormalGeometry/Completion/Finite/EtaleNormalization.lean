import OAI.AlgebraicGeometry.FormalGeometry.Completion.SmoothBaseFiniteNormalization
import OAI.AlgebraicGeometry.FormalGeometry.Completion.SchemeFlatCompositionDescent
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Etale Normalization -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.EtaleNormalization.Construction

noncomputable section

/-!
# Completion: the actual normalization factor is finite étale

Smoothness of the first factor gives faithful flatness on its local
rings. Flatness of the original family descends to the integral factor.
Combined with proved finiteness and formal unramifiedness, this gives
finite étaleness without adding a geometric hypothesis on that factor.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

/-- Flatness of the actual integral normalization factor. -/
theorem proper_smooth_fromNormalization_flat (K : Type u) [Field K]
    {X Y : Scheme.{u}} [ConnectedSpace X]
    (pX : X ⟶ Spec (CommRingCat.of K)) [IsProper pX] [Smooth pX]
    (f : X ⟶ Y) [IsProper f] [Smooth f] : Flat f.fromNormalization := by
  have : Smooth f.toNormalization := SmoothToNormalization.Construction.proper_smooth_toNormalization_smooth K pX f
  have : Surjective f.toNormalization := Proper.Normalization.Construction.proper_toNormalization_surjective f
  have : Flat (f.toNormalization ≫ f.fromNormalization) := by
    rw [Scheme.Hom.toNormalization_fromNormalization]
    infer_instance
  exact SchemeFlatCompositionDescent.Construction.scheme_flat_of_surjective_flat_composition f.toNormalization f.fromNormalization

/-- The actual integral factor of a proper smooth family of smooth integral field schemes
is finite étale. -/
theorem proper_smooth_fromNormalization_finite_etale (K : Type u) [Field K]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (pX : X ⟶ Spec (CommRingCat.of K)) [IsProper pX] [Smooth pX]
    (pY : Y ⟶ Spec (CommRingCat.of K)) [Smooth pY]
    (f : X ⟶ Y) [IsProper f] [Smooth f] [Surjective f] :
    IsFinite f.fromNormalization ∧ Etale f.fromNormalization := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian pY
  have : IsFinite f.fromNormalization := SmoothBaseFiniteNormalization.Construction.proper_smooth_fromNormalization_finite K pX pY f
  have : Flat f.fromNormalization := proper_smooth_fromNormalization_flat K pX f
  have : FormallyUnramified f.fromNormalization :=
    UnramifiedNormalization.Construction.proper_smooth_fromNormalization_formallyUnramified K pX f
  exact ⟨inferInstance, Etale.of_formallyUnramified_of_flat f.fromNormalization⟩

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.EtaleNormalization.Construction
