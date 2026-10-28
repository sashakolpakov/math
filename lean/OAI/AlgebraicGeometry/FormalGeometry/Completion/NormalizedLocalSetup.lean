import OAI.AlgebraicGeometry.FormalGeometry.Completion.NormalizedLocalFunctions
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.SmoothFiniteEtaleNormalization
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.SmoothToNormalization
import OAI.AlgebraicGeometry.FormalGeometry.Completion.ComparisonInjective

/-! # Normalized Local Setup -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.NormalizedLocalSetup.Construction

noncomputable section

/-!
# Completion: the actual Noetherian local normalization family

The local base is the stalk of the actual relative normalization. Its
Noetherian property, and the properness, smoothness, surjectivity, and
global-function identification of the actual family are proved from the
original proper smooth geometry. No connected-fiber premise is used.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

/-- All local hypotheses used for the actual normalized formal-functions comparison follow
from the original proper smooth family. -/
theorem proper_smooth_normalizedLocalFamily_properties (K : Type u) [Field K]
    {X Y : Scheme.{u}} [IsIntegral Y]
    (pX : X ⟶ Spec (CommRingCat.of K)) [IsProper pX] [Smooth pX]
    (pY : Y ⟶ Spec (CommRingCat.of K)) [Smooth pY]
    (f : X ⟶ Y) [IsProper f] [Smooth f] (n : f.normalization) :
    IsNoetherianRing (f.normalization.presheaf.stalk n) ∧
      IsProper (NormalizedLocalFunctions.Construction.normalizedLocalFamily f n) ∧ Smooth (NormalizedLocalFunctions.Construction.normalizedLocalFamily f n) ∧
      Surjective (NormalizedLocalFunctions.Construction.normalizedLocalFamily f n) ∧ IsIso (NormalizedLocalFunctions.Construction.normalizedLocalFamily f n).appTop := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian pY
  have : IsFinite f.fromNormalization :=
    (Proper.SmoothFiniteEtaleNormalization.Construction.proper_smooth_family_normalization_finite_etale K pX pY f).1
  have : IsLocallyNoetherian f.normalization :=
    LocallyOfFiniteType.isLocallyNoetherian f.fromNormalization
  have : Smooth f.toNormalization := Proper.SmoothToNormalization.Construction.proper_smooth_family_toNormalization_smooth K pX f
  have : Surjective f.toNormalization := Proper.Normalization.Construction.proper_toNormalization_surjective f
  have : Smooth (NormalizedLocalFunctions.Construction.normalizedLocalFamily f n) := by unfold NormalizedLocalFunctions.Construction.normalizedLocalFamily; infer_instance
  have : Surjective (NormalizedLocalFunctions.Construction.normalizedLocalFamily f n) := by unfold NormalizedLocalFunctions.Construction.normalizedLocalFamily; infer_instance
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    NormalizedLocalFunctions.Construction.normalizedLocalFamily_appTop_isIso f n⟩

/-- The canonical comparison for the actual family over the local ring of its normalization. -/
def normalizedLocalFormalComparison {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (n : f.normalization) :=
  FunctionsComparison.Construction.formalFunctionsComparison (IsLocalRing.maximalIdeal (f.normalization.presheaf.stalk n))
    (NormalizedLocalFunctions.Construction.normalizedLocalFamily f n)

/-- The actual normalized local comparison is injective, derived from the original smooth family. -/
theorem normalizedLocalFormalComparison_injective (K : Type u) [Field K]
    {X Y : Scheme.{u}} (pX : X ⟶ Spec (CommRingCat.of K)) [IsProper pX] [Smooth pX]
    (f : X ⟶ Y) [IsProper f] [Smooth f] (n : f.normalization) :
    Function.Injective (normalizedLocalFormalComparison f n) := by
  have : Smooth f.toNormalization := Proper.SmoothToNormalization.Construction.proper_smooth_family_toNormalization_smooth K pX f
  have : Surjective f.toNormalization := Proper.Normalization.Construction.proper_toNormalization_surjective f
  have : Smooth (NormalizedLocalFunctions.Construction.normalizedLocalFamily f n) := by unfold NormalizedLocalFunctions.Construction.normalizedLocalFamily; infer_instance
  have : Surjective (NormalizedLocalFunctions.Construction.normalizedLocalFamily f n) := by unfold NormalizedLocalFunctions.Construction.normalizedLocalFamily; infer_instance
  exact ComparisonInjective.Construction.formalFunctionsComparison_injective _ (NormalizedLocalFunctions.Construction.normalizedLocalFamily f n)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.NormalizedLocalSetup.Construction
