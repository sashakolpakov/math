import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Family Map Square -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.FamilyMapSquare

noncomputable section

/-! The family map induced by a morphism is its actual pullback along the second projection. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
universe u
variable {S : Scheme.{u}} (T : Over S) {X Y : Over S} (f : X ⟶ Y)

theorem cartesianFamilyMapSquare :
    IsPullback (snd T X) (T ◁ f) f (snd T Y) where
  isLimit' := ⟨Limits.PullbackCone.isLimitAux' _ (fun s => by
    change { l : s.pt ⟶ T ⊗ X // l ≫ snd T X = s.fst ∧ l ≫ (T ◁ f) = s.snd ∧
      ∀ {m : s.pt ⟶ T ⊗ X}, m ≫ snd T X = s.fst → m ≫ (T ◁ f) = s.snd → m = l }
    refine ⟨lift (s.snd ≫ fst T Y) s.fst, ?_, ?_, ?_⟩
    · exact lift_snd _ _
    · apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, whiskerLeft_fst, lift_fst]
      · rw [Category.assoc, whiskerLeft_snd, ← Category.assoc, lift_snd]
        exact s.condition
    · intro m h₁ h₂
      apply CartesianMonoidalCategory.hom_ext
      · simpa only [Category.assoc, whiskerLeft_fst, lift_fst] using
          congrArg (fun k => k ≫ fst T Y) h₂
      · simpa only [lift_snd] using h₁)⟩

theorem cartesianFamilyMapSquare_left :
    IsPullback (snd T X).left (T ◁ f).left f.left (snd T Y).left :=
  (cartesianFamilyMapSquare T f).map (Over.forget S)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.FamilyMapSquare
