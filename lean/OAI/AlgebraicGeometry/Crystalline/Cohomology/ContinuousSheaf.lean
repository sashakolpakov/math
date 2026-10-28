import Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Sites.Abelian

/-! # Continuous Sheaf -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.ContinuousSheaf.ContinuousSheafLimits

noncomputable section

/-! # Limits and additivity of restriction along continuous site functors -/

open _root_.CategoryTheory Limits

universe u₁ u₂ v₁ v₂ u₃ v₃ u₄ v₄

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [F.IsContinuous J K] (A : Type u₃) [Category.{v₃} A]

theorem preservesLimitsOfShape (I : Type u₄) [Category.{v₄} I] [HasLimitsOfShape I A] :
    PreservesLimitsOfShape I (F.sheafPushforwardContinuous A J K) := by
  have : PreservesLimitsOfShape I
      (F.sheafPushforwardContinuous A J K ⋙ sheafToPresheaf J A) :=
    preservesLimitsOfShape_of_natIso (F.sheafPushforwardContinuousCompSheafToPresheafIso A J K).symm
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (sheafToPresheaf J A)

theorem preservesFiniteLimits [HasFiniteLimits A] :
    PreservesFiniteLimits (F.sheafPushforwardContinuous A J K) where
  preservesFiniteLimits I _ _ := preservesLimitsOfShape F J K A I

theorem additive [Preadditive A] : (F.sheafPushforwardContinuous A J K).Additive where
  map_add := rfl

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.ContinuousSheaf.ContinuousSheafLimits
