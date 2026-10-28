import OAI.RepresentationTheory.Theta.Geometric.MultiplicativeFamilyCriterion

/-! # Multiplicative Family Base Change -/

namespace OAI.RepresentationTheory.Theta.Geometric.MultiplicativeFamilyBaseChange

noncomputable section

/-! The universal tensor identity commutes with actual parameter
pullback and can be checked as an isomorphism of two fixed line bundles. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u
variable {S : Scheme.{u}}

theorem constantFamilyClass_square {A B T U : Over S} (j : U ⟶ T) (f : B ⟶ A)
    (q : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A).left) :
    Picard.PicardPullback.picardPullback (j ▷ B).left (Picard.PicardPullback.picardPullback (T ◁ f).left q) =
      Picard.PicardPullback.picardPullback (U ◁ f).left (Picard.PicardPullback.picardPullback (j ▷ A).left q) := by
  rw [Picard.PicardPullback.picardPullback_comp, Picard.PicardPullback.picardPullback_comp]
  have h : (j ▷ B) ≫ (T ◁ f) = (U ◁ f) ≫ (j ▷ A) := by
    apply hom_ext <;> simp
  exact congrArg (fun a => Picard.PicardPullback.picardPullback a q) (congrArg Over.Hom.left h)

theorem multiplicativeFamilyBaseChangeIso_iff {g : ℕ} (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    {T U : Over S} (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (T ⊗ A.scheme).left) (j : U ⟶ T) :
    MultiplicativeFamilyCriterion.IsMultiplicativeFamilyClass A U (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (j ▷ A.scheme).left)) ↔
      Nonempty (((L.pullback (T ◁ (fst A.scheme A.scheme * snd A.scheme A.scheme)).left).pullback
        (j ▷ (A.scheme ⊗ A.scheme)).left).sheaf ≅
      (((L.pullback (T ◁ fst A.scheme A.scheme).left).tensor
        (L.pullback (T ◁ snd A.scheme A.scheme).left)).pullback
          (j ▷ (A.scheme ⊗ A.scheme)).left).sheaf) := by
  constructor
  · intro h
    suffices he : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf
        ((L.pullback (T ◁ (fst A.scheme A.scheme * snd A.scheme A.scheme)).left).pullback
          (j ▷ (A.scheme ⊗ A.scheme)).left) =
        AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (((L.pullback (T ◁ fst A.scheme A.scheme).left).tensor
          (L.pullback (T ◁ snd A.scheme A.scheme).left)).pullback
            (j ▷ (A.scheme ⊗ A.scheme)).left) from Quotient.exact he
    change Picard.PicardPullback.picardPullback _ (Picard.PicardPullback.picardPullback _ (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) =
      Picard.PicardPullback.picardPullback _ (Picard.PicardPullback.picardPullback _ (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) * Picard.PicardPullback.picardPullback _ (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L))
    rw [map_mul, constantFamilyClass_square, constantFamilyClass_square, constantFamilyClass_square]
    exact h
  · intro h
    have he := Quotient.sound (s := AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.isoSetoid _) h
    change Picard.PicardPullback.picardPullback _ (Picard.PicardPullback.picardPullback _ (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) =
      Picard.PicardPullback.picardPullback _ (Picard.PicardPullback.picardPullback _ (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) * Picard.PicardPullback.picardPullback _ (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) at he
    rw [map_mul, constantFamilyClass_square, constantFamilyClass_square, constantFamilyClass_square] at he
    exact he

end

end OAI.RepresentationTheory.Theta.Geometric.MultiplicativeFamilyBaseChange
