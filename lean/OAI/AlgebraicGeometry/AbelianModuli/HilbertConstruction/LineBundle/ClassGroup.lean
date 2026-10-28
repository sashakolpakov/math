import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.ClassMonoid
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TensorInverse
import Mathlib.Algebra.Group.Units.Defs

/-! # Class Group -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The constructed reciprocal-frame line bundle supplies inverses in the
existing commutative monoid of actual line-bundle isomorphism classes. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {X : Scheme.{u}}

theorem Line.Bundles.LineBundle.isUnit_isoClass (q : Line.Bundles.LineBundle.IsoClass X) : IsUnit q := by
  induction q using Quotient.inductionOn with
  | h L =>
    refine ⟨{ val := Line.Bundles.LineBundle.classOf L
              inv := Line.Bundles.LineBundle.classOf L.reciprocalFrameBundle
              val_inv := ?_
              inv_val := ?_ }, rfl⟩
    · exact Quotient.sound ⟨L.tensorReciprocalFrameIso⟩
    · exact Quotient.sound ⟨L.reciprocalFrameTensorIso⟩

instance Line.Bundles.LineBundle.isoClassCommGroup (X : Scheme.{u}) : CommGroup (Line.Bundles.LineBundle.IsoClass X) :=
  commGroupOfIsUnit Line.Bundles.LineBundle.isUnit_isoClass

theorem Line.Bundles.LineBundle.classOf_reciprocalFrameBundle (L : Line.Bundles.LineBundle X) :
    Line.Bundles.LineBundle.classOf L.reciprocalFrameBundle = (Line.Bundles.LineBundle.classOf L)⁻¹ := by
  have h : Line.Bundles.LineBundle.classOf L * Line.Bundles.LineBundle.classOf L.reciprocalFrameBundle = 1 :=
    Quotient.sound ⟨L.tensorReciprocalFrameIso⟩
  calc
    Line.Bundles.LineBundle.classOf L.reciprocalFrameBundle = (Line.Bundles.LineBundle.classOf L)⁻¹ * Line.Bundles.LineBundle.classOf L * Line.Bundles.LineBundle.classOf L.reciprocalFrameBundle := by
      rw [inv_mul_cancel, one_mul]
    _ = (Line.Bundles.LineBundle.classOf L)⁻¹ * (Line.Bundles.LineBundle.classOf L * Line.Bundles.LineBundle.classOf L.reciprocalFrameBundle) := mul_assoc _ _ _
    _ = (Line.Bundles.LineBundle.classOf L)⁻¹ := by rw [h, mul_one]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
