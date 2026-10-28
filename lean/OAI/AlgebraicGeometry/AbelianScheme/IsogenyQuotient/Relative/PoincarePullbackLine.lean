import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.RigidifiedLine
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledPoincareDetection
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledHomogeneousPullback

/-! # Poincare Pullback Line -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.PoincarePullbackLine.Construction

noncomputable section

section

/-! Pull back the original normalized Poincare bundle along the
group factor, retaining its actual origin frame and its Picard value. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]
  (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (f : B ⟶ A) [IsMonHom f]

set_option backward.isDefEq.respectTransparency false in
def relativePoincarePullbackLine : RigidifiedLine.Construction.RelativeRigidifiedProductLine B D.abelian where
  bundle := D.poincare.pullback (D.abelian ◁ f).left
  axis := FormalGeometry.Completion.Rigidified.FrameScalar.Construction.rigidificationBaseChangeIso (D.abelian ◁ f).left
    (lift (𝟙 D.abelian) (1 : D.abelian ⟶ B)).left (𝟙 D.abelian.left)
    (lift (𝟙 D.abelian) (1 : D.abelian ⟶ A)).left
    (congrArg Over.Hom.left (show lift (𝟙 D.abelian) (1 : D.abelian ⟶ B) ≫
      (D.abelian ◁ f) = 𝟙 D.abelian ≫ lift (𝟙 D.abelian) (1 : D.abelian ⟶ A) by simp))
    D.poincare.sheaf (Classical.choice D.normalizedAtAbelianZero)

theorem relativePoincarePullbackLine_homogeneous : Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.IsHomogeneousPicardClass B D.abelian
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (relativePoincarePullbackLine D f).bundle) :=
  Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardClass_pullback B A f D.poincareHomogeneous

set_option backward.isDefEq.respectTransparency false in
theorem relativePoincarePullbackLine_class {T : Over S} (a : T ⟶ D.abelian) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf ((relativePoincarePullbackLine D f).line a) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (T ◁ f).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (a ▷ A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare)) := by
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (a ⊗ₘ 𝟙 B).left
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (D.abelian ◁ f).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare)) = _
  rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]
  apply congrArg (fun t => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass t (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare))
  exact congrArg Over.Hom.left (show (a ⊗ₘ 𝟙 B) ≫ (D.abelian ◁ f) =
    (T ◁ f) ≫ (a ▷ A) by simpa using (whisker_exchange a f).symm)

set_option backward.isDefEq.respectTransparency false in
theorem relativePoincarePullbackLine_value {T : Over S} (a : T ⟶ D.abelian) :
    (relativePoincarePullbackLine D f).relativeValue a =
      (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheafInclusion B).hom.app (op T)
        ((Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullback B A f).hom.app (op T) (D.representable.homEquiv a)) := by
  unfold RigidifiedLine.Construction.RelativeRigidifiedProductLine.relativeValue
  rw [relativePoincarePullbackLine_class]
  change (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard B).app (op T)
    ((Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullbackPresheaf f).app (op T)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (a ▷ A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare))) = _
  rw [← Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullback_toRelativePicard_apply]
  change (Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullback f).hom.app (op T) (Picard.Homomorphisms.UnbundledPoincareDetection.Construction.UnbundledPicard.poincareClass D a) = _
  rw [Picard.Homomorphisms.UnbundledPoincareDetection.Construction.UnbundledPicard.poincareClass_eq_representation]
  exact (congrArg (fun p : Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf A ⟶ AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf B =>
    p.hom.app (op T) (D.representable.homEquiv a))
      (Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullback_inclusion B A f)).symm

end

/-! Pullback of the original Poincare bundle retains the second
origin normalization as an equality of actual line-bundle classes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]
  (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (f : B ⟶ A) [IsMonHom f]

set_option backward.isDefEq.respectTransparency false in
theorem relativePoincarePullbackLine_secondAxis_class :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (lift (1 : B ⟶ D.abelian) (𝟙 B)).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (relativePoincarePullbackLine D f).bundle) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass B.left := by
  have h : (lift (1 : B ⟶ D.abelian) (𝟙 B)).left ≫ (D.abelian ◁ f).left =
      f.left ≫ (lift (1 : A ⟶ D.abelian) (𝟙 A)).left :=
    congrArg Over.Hom.left (by simp : lift (1 : B ⟶ D.abelian) (𝟙 B) ≫ (D.abelian ◁ f) =
      f ≫ lift (1 : A ⟶ D.abelian) (𝟙 A))
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (lift (1 : B ⟶ D.abelian) (𝟙 B)).left
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (D.abelian ◁ f).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare)) = _
  rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, h, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]
  have hz : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (lift (1 : A ⟶ D.abelian) (𝟙 A)).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass A.left :=
    Quotient.sound D.normalizedAtDualZero
  rw [hz, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_trivial]

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.PoincarePullbackLine.Construction
