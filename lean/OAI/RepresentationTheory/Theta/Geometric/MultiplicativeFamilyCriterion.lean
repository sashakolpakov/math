import OAI.RepresentationTheory.Theta.Geometric.Picard.PicardPullback
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.LineNormalization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.Picard

/-! # Multiplicative Family Criterion -/

namespace OAI.RepresentationTheory.Theta.Geometric.MultiplicativeFamilyCriterion

noncomputable section

/-! One actual tensor identity over the universal pair of points
implies translation invariance on every test scheme. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u
variable {S : Scheme.{u}} {g : ℕ} (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)

def IsMultiplicativeFamilyClass (T : Over S) (q : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A.scheme).left) : Prop :=
  Picard.PicardPullback.picardPullback (T ◁ (fst A.scheme A.scheme * snd A.scheme A.scheme)).left q =
    Picard.PicardPullback.picardPullback (T ◁ fst A.scheme A.scheme).left q *
      Picard.PicardPullback.picardPullback (T ◁ snd A.scheme A.scheme).left q

theorem homogeneous_of_multiplicative_family {T : Over S}
    (q : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A.scheme).left) (hq : IsMultiplicativeFamilyClass A T q) :
    A.IsHomogeneousPicardClass T q := by
  intro U f a
  let d : U ⊗ A.scheme ⟶ T ⊗ (A.scheme ⊗ A.scheme) :=
    lift (fst U A.scheme ≫ f) (lift (fst U A.scheme ≫ a) (snd U A.scheme))
  have hm : d ≫ T ◁ (fst A.scheme A.scheme * snd A.scheme A.scheme) =
      A.translation a ≫ (f ▷ A.scheme) := by
    apply hom_ext <;> simp [d, AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.translation, MonObj.comp_mul]
  have h₁ : d ≫ T ◁ fst A.scheme A.scheme = fst U A.scheme ≫ lift f a := by
    apply hom_ext <;> simp [d]
  have h₂ : d ≫ T ◁ snd A.scheme A.scheme = f ▷ A.scheme := by
    apply hom_ext <;> simp [d]
  have h := congrArg (Picard.PicardPullback.picardPullback d.left) hq
  change Picard.PicardPullback.picardPullback d.left (Picard.PicardPullback.picardPullback _ q) =
    Picard.PicardPullback.picardPullback d.left (Picard.PicardPullback.picardPullback _ q * Picard.PicardPullback.picardPullback _ q) at h
  rw [map_mul, Picard.PicardPullback.picardPullback_comp, Picard.PicardPullback.picardPullback_comp, Picard.PicardPullback.picardPullback_comp,
    ← Over.comp_left, hm, ← Over.comp_left, h₁, ← Over.comp_left, h₂] at h
  rw [Over.comp_left, Over.comp_left, ← Picard.PicardPullback.picardPullback_comp, ← Picard.PicardPullback.picardPullback_comp] at h
  exact (congrArg ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U)) h).trans
    (AlgebraicGeometry.FormalGeometry.Completion.RelativePicard.Construction.RelativePicardBaseTwist.toRelativePicard_baseTwist_class A.scheme
      (Picard.PicardPullback.picardPullback (lift f a).left q) (Picard.PicardPullback.picardPullback (f ▷ A.scheme).left q))

end

end OAI.RepresentationTheory.Theta.Geometric.MultiplicativeFamilyCriterion
