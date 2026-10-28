import OAI.AlgebraicGeometry.Picard.PoincareBundle.Finite.GroupLineFrame
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Finite.GroupCocycleSplitting
import OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalNormalizedLineFrame
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.NaturalSchemeCocycle
import OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicativeFrameCorrection

/-! # Group Multiplicative Splitting -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Finite.GroupMultiplicativeSplitting

noncomputable section

/-! Split commutative multiplicative lines on actual finite commutative group schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicativeLineData

variable (k : Type u) [Field k] [IsAlgClosed k] (H : Over (Spec (.of k)))
  [GrpObj H] [IsCommMonObj H] [IsFinite H.hom]
  (L : Line.Bundles.LineBundle H.left) (D : MultiplicativeLineData.MultiplicativeData L)
  (hcomm : ∀ {T : Over (Spec (.of k))} (a b c : T ⟶ H) (hab : a * b = c) (hba : b * a = c)
    (U : T.left.Opens) (s : Γ(Line.Fibers.fiber L a, U)) (t : Γ(Line.Fibers.fiber L b, U)),
      (D.product a b c hab).app U s t = (D.product b a c hba).app U t s)

include hcomm

/-- All frames and their laws are constructed from the finite group and the commutative multiplication. -/
theorem exists_multiplicative_frames :
    ∃ F : ∀ {T : Over (Spec (.of k))} (a : T ⟶ H), AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Line.Fibers.fiber L a,
      (∀ T : Over (Spec (.of k)), F (1 : T ⟶ H) = D.unitFrame) ∧
      (∀ {T U : Over (Spec (.of k))} (g : U ⟶ T) (a : T ⟶ H) (a' : U ⟶ H) (ha : g ≫ a = a'),
        Line.Fibers.pullSection L g a a' ha (F a).hom = (F a').hom) ∧
      ∀ (T : Over (Spec (.of k))) (a b c : T ⟶ H) (hab : a * b = c) (V : T.left.Opens),
        (D.product a b c hab).app V ((F a).hom.app V (1 : Γ(T.left, V)))
          ((F b).hom.app V (1 : Γ(T.left, V))) = (F c).hom.app V (1 : Γ(T.left, V)) := by
  obtain ⟨F, hFone, hFnat⟩ := GlobalNormalizedLineFrame.exists_normalized_frames (H := H) L D
    (GroupLineFrame.exists_frame k H L)
  let C := Line.NaturalSchemeCocycle.cocycle (H := H) L D F hFone hFnat hcomm
  obtain ⟨v, hvone, hvnat, hvmul⟩ := GroupCocycleSplitting.exists_splitting k H C
  refine ⟨fun {T} a => MultiplicativeFrameCorrection.frame (H := H) L F v a, ?_, ?_, ?_⟩
  · intro T
    exact MultiplicativeFrameCorrection.frame_one (H := H) L D F v T (hFone T) (hvone T)
  · intro T U g a a' ha
    exact MultiplicativeFrameCorrection.frame_natural (H := H) L F v g a a' ha (hFnat g a a' ha)
      ((hvnat g a).trans (congrArg (v U) ha))
  · intro T a b c hab V
    have hm : MultiplicativeLineCocycle.value L D F a b c hab * v T c = v T a * v T b := by
      subst c
      exact hvmul T a b
    exact MultiplicativeFrameCorrection.frame_product (H := H) L D F v a b c hab hm V

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Finite.GroupMultiplicativeSplitting
