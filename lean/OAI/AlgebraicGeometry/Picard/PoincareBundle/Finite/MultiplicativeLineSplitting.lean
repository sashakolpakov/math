import OAI.AlgebraicGeometry.Picard.PoincareBundle.Finite.NormalizedLineFrame
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.NaturalSchemeCocycle
import OAI.AlgebraicGeometry.Picard.PoincareBundle.SchemeCocycleSplitting
import OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicativeFrameCorrection

/-! # Multiplicative Line Splitting -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Finite.MultiplicativeLineSplitting

noncomputable section

/-! Every commutative multiplicative line on a finite commutative group over an algebraically closed field splits. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicativeLineData

variable (k R : Type u) [Field k] [IsAlgClosed k] [CommRing R] [HopfAlgebra k R]
  [Coalgebra.IsCocomm k R] [Module.Finite k R]
  (L : Line.Bundles.LineBundle (Spec (.of R)))
  (D : MultiplicativeLineData.MultiplicativeData (A := (Spec (.of R)).asOver (Spec (.of k))) L)
  (hcomm : ∀ {T : Over (Spec (.of k))}
    (a b c : T ⟶ (Spec (.of R)).asOver (Spec (.of k))) (hab : a * b = c) (hba : b * a = c)
    (U : T.left.Opens) (s : Γ(Line.Fibers.fiber L a, U)) (t : Γ(Line.Fibers.fiber L b, U)),
      (D.product a b c hab).app U s t = (D.product b a c hba).app U t s)

include hcomm

/-- The splitting consists of actual natural sheaf frames and is valid on every infinitesimal test scheme. -/
theorem exists_multiplicative_frames :
    ∃ F : ∀ {T : Over (Spec (.of k))} (a : T ⟶ (Spec (.of R)).asOver (Spec (.of k))),
        AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Line.Fibers.fiber L a,
      (∀ T : Over (Spec (.of k)),
        F (1 : T ⟶ (Spec (.of R)).asOver (Spec (.of k))) = D.unitFrame) ∧
      (∀ {T U : Over (Spec (.of k))} (g : U ⟶ T)
          (a : T ⟶ (Spec (.of R)).asOver (Spec (.of k)))
          (a' : U ⟶ (Spec (.of R)).asOver (Spec (.of k))) (ha : g ≫ a = a'),
        Line.Fibers.pullSection L g a a' ha (F a).hom = (F a').hom) ∧
      ∀ (T : Over (Spec (.of k))) (a b c : T ⟶ (Spec (.of R)).asOver (Spec (.of k)))
          (hab : a * b = c) (V : T.left.Opens),
        (D.product a b c hab).app V ((F a).hom.app V (1 : Γ(T.left, V)))
          ((F b).hom.app V (1 : Γ(T.left, V))) = (F c).hom.app V (1 : Γ(T.left, V)) := by
  obtain ⟨F, hFone, hFnat⟩ := NormalizedLineFrame.exists_normalized_frames k R L D
  let C := Line.NaturalSchemeCocycle.cocycle (S := Spec (.of k)) (H := (Spec (.of R)).asOver (Spec (.of k))) L D F hFone hFnat hcomm
  obtain ⟨a, haone, hamul⟩ := SchemeCocycleSplitting.exists_regular_splitting k R C
  let v := CocycleSchemeValues.solution k R a
  refine ⟨fun {T} x => MultiplicativeFrameCorrection.frame (S := Spec (.of k)) (H := (Spec (.of R)).asOver (Spec (.of k))) L F v x, ?_, ?_, ?_⟩
  · intro T
    exact MultiplicativeFrameCorrection.frame_one (S := Spec (.of k)) (H := (Spec (.of R)).asOver (Spec (.of k))) L D F v T (hFone T) (haone T)
  · intro T U g x x' hx
    have hv : Units.map g.left.appTop.hom (v T x) = v U x' :=
      (CocycleSchemeValues.solution_natural k R a g x).trans
        (congrArg (v U) hx)
    exact MultiplicativeFrameCorrection.frame_natural (S := Spec (.of k)) (H := (Spec (.of R)).asOver (Spec (.of k))) L F v g x x' hx (hFnat g x x' hx) hv
  · intro T x y z hxy V
    have hm : MultiplicativeLineCocycle.value L D F x y z hxy * v T z = v T x * v T y := by
      subst z
      exact hamul T x y
    exact MultiplicativeFrameCorrection.frame_product (S := Spec (.of k)) (H := (Spec (.of R)).asOver (Spec (.of k))) L D F v x y z hxy hm V

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Finite.MultiplicativeLineSplitting
