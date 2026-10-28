import OAI.AlgebraicGeometry.Picard.PoincareBundle.RelativeBaseTwist
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ParameterRecovery

/-! # Homogeneity -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.Homogeneity

noncomputable section

/-!
# The vertical product constructs homogeneous relative Picard classes

Only the actual invertible global product is needed: its associativity is not
used to prove an equality of isomorphism classes.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Bundles OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.LineBundles OAI.AlgebraicGeometry.Picard.PoincareBundle.Functor OAI.AlgebraicGeometry.Picard.PoincareBundle.Homogeneous
open OAI.AlgebraicGeometry.Picard.PoincareBundle.RelativeBaseTwist OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ProductParameters
open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

variable {S : Scheme.{u}} {B A : Over S}
  (R : Line.Bundles.LineBundle (B ⊗ A).left)

/-- The actual relative line class obtained by evaluating the first family parameter. -/
def familyClass {T : Over S} (x : T ⟶ B) : (Functor.relativePicardPresheaf A).obj (op T) :=
  Line.Bundles.LineBundleClass.pullback (x ⊗ₘ 𝟙 A).left (Line.Bundles.LineBundleClass.mk R)

/-- These family classes commute with every test-scheme change. -/
theorem familyClass_natural {T U : Over S} (h : U ⟶ T) (x : T ⟶ B) :
    (Functor.relativePicardPresheaf A).map h.op (familyClass R x) = familyClass R (h ≫ x) := by
  change Line.Bundles.LineBundleClass.pullback (h ⊗ₘ 𝟙 A).left
    (Line.Bundles.LineBundleClass.pullback (x ⊗ₘ 𝟙 A).left (Line.Bundles.LineBundleClass.mk R)) = _
  rw [← Line.Bundles.LineBundleClass.pullback_comp]
  have hs : (h ⊗ₘ 𝟙 A).left ≫ (x ⊗ₘ 𝟙 A).left = ((h ≫ x) ⊗ₘ 𝟙 A).left :=
    congrArg Over.Hom.left (by simp : (h ⊗ₘ 𝟙 A) ≫ (x ⊗ₘ 𝟙 A) = (h ≫ x) ⊗ₘ 𝟙 A)
  rw [hs]
  rfl

variable [GrpObj A]
  (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Line.Fibers.fiber R (ProductParameters.inputLeft B A)) (Line.Fibers.fiber R (ProductParameters.inputRight B A))
    (Line.Fibers.fiber R (ProductParameters.outputPoint B A)))
  (hβ : IsIso (Bilinear.BilinearPullback.toHom β))

include β hβ

/-- An invertible global vertical product gives the actual tensor-class equation on every test scheme. -/
theorem productClass {T : Over S} (a b c : T ⟶ B ⊗ A)
    (h : FiberwiseMultiplication.ProductRel (snd B A) (fst B A) a b c) :
    Tensor.LineBundles.tensorClass (Line.Bundles.LineBundleClass.pullback a.left (Line.Bundles.LineBundleClass.mk R))
        (Line.Bundles.LineBundleClass.pullback b.left (Line.Bundles.LineBundleClass.mk R)) =
      Line.Bundles.LineBundleClass.pullback c.left (Line.Bundles.LineBundleClass.mk R) := by
  let e := @asIso _ _ _ _ (Bilinear.BilinearPullback.toHom
    (ParameterRecovery.product R β a b c h))
    (ParameterRecovery.product_isIso R β hβ a b c h)
  exact Quotient.sound ⟨e⟩

/-- Translation of a fiber differs from it by an actual line pulled back from the test scheme. -/
theorem translatedClass {T : Over S} (x : T ⟶ B) (a : T ⟶ A) :
    Line.Bundles.LineBundleClass.pullback (Homogeneous.translation A a).left (familyClass R x) =
      RelativeBaseTwist.baseTwist A (Line.Bundles.LineBundleClass.pullback (lift x a).left (Line.Bundles.LineBundleClass.mk R))
        (familyClass R x) := by
  have hp : FiberwiseMultiplication.ProductRel (snd B A) (fst B A)
      (fst T A ≫ lift x a) (x ⊗ₘ 𝟙 A) (Homogeneous.translation A a ≫ (x ⊗ₘ 𝟙 A)) := by
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [Homogeneous.translation]
  have hc := productClass R β hβ _ _ _ hp
  change Line.Bundles.LineBundleClass.pullback (Homogeneous.translation A a).left
      (Line.Bundles.LineBundleClass.pullback (x ⊗ₘ 𝟙 A).left (Line.Bundles.LineBundleClass.mk R)) =
    Tensor.LineBundles.tensorClass (Line.Bundles.LineBundleClass.pullback (fst T A).left
      (Line.Bundles.LineBundleClass.pullback (lift x a).left (Line.Bundles.LineBundleClass.mk R))) _
  rw [← Line.Bundles.LineBundleClass.pullback_comp, ← Line.Bundles.LineBundleClass.pullback_comp]
  exact hc.symm

/-- The actual vertical product makes every evaluated family class homogeneous. -/
theorem familyClass_isHomogeneous {T : Over S} (x : T ⟶ B) :
    Homogeneous.IsHomogeneous A T (familyClass R x) := by
  intro U h a
  rw [familyClass_natural]
  erw [translatedClass R β hβ]
  exact RelativeBaseTwist.toRelativePicard_baseTwist A (R.pullback (lift (h ≫ x) a).left) (familyClass R (h ≫ x))

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.Homogeneity
