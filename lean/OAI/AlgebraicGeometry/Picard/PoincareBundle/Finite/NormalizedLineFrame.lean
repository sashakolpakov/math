import OAI.AlgebraicGeometry.Picard.PoincareBundle.Finite.AffineLineFrame
import OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalNormalizedLineFrame
import Mathlib.AlgebraicGeometry.Group.Affine

/-! # Normalized Line Frame -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Finite.NormalizedLineFrame

noncomputable section

/-! Normalized natural frames for a line on a finite affine group over a field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicativeLineData

variable (k R : Type u) [Field k] [CommRing R] [Algebra k R] [Module.Finite k R]
  [GrpObj ((Spec (.of R)).asOver (Spec (.of k)))]
  (L : Line.Bundles.LineBundle (Spec (.of R)))
  (D : MultiplicativeLineData.MultiplicativeData (A := (Spec (.of R)).asOver (Spec (.of k))) L)

/-- Finite semilocal triviality and scalar normalization construct all the fiber frames. -/
theorem exists_normalized_frames :
    ∃ F : ∀ {T : Over (Spec (.of k))} (a : T ⟶ (Spec (.of R)).asOver (Spec (.of k))),
        AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Line.Fibers.fiber L a,
      (∀ T : Over (Spec (.of k)),
        F (1 : T ⟶ (Spec (.of R)).asOver (Spec (.of k))) = D.unitFrame) ∧
      ∀ {T U : Over (Spec (.of k))} (g : U ⟶ T)
          (a : T ⟶ (Spec (.of R)).asOver (Spec (.of k)))
          (a' : U ⟶ (Spec (.of R)).asOver (Spec (.of k))) (ha : g ≫ a = a'),
        Line.Fibers.pullSection L g a a' ha (F a).hom = (F a').hom :=
  GlobalNormalizedLineFrame.exists_normalized_frames
    (S := Spec (.of k)) (H := (Spec (.of R)).asOver (Spec (.of k))) L D
    (AffineLineFrame.exists_frame k R L)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Finite.NormalizedLineFrame
