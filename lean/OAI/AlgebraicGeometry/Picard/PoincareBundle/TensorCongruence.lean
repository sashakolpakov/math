import OAI.AlgebraicGeometry.Picard.PoincareBundle.SheafifiedBinaryCongruence
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.LineBundles
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Homogeneous
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-! # Tensor Congruence -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.TensorCongruence

noncomputable section

/-! Tensor products of actual line classes respect their relative Picard sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Bundles OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.LineBundles OAI.AlgebraicGeometry.Picard.PoincareBundle.Functor OAI.AlgebraicGeometry.Picard.PoincareBundle.Homogeneous

variable {S : Scheme.{u}} (A : Over S)

/-- Equality of relative Picard sections is a congruence for actual line tensor products. -/
theorem tensor_congr {T : Over S} {q q' r r' : (Functor.relativePicardPresheaf A).obj (op T)}
    (hq : (Functor.toRelativePicard A).app (op T) q = (Functor.toRelativePicard A).app (op T) q')
    (hr : (Functor.toRelativePicard A).app (op T) r = (Functor.toRelativePicard A).app (op T) r') :
    (Functor.toRelativePicard A).app (op T) (Tensor.LineBundles.tensorClass q r) =
      (Functor.toRelativePicard A).app (op T) (Tensor.LineBundles.tensorClass q' r') := by
  have : Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) (Functor.toRelativePicard A) :=
    inferInstanceAs (Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S)
      (toSheafify (Scheme.fppfTopology.over S) (Functor.relativePicardPresheaf A)))
  exact SheafifiedBinaryCongruence.binary_congr (C := Over S) (F := Functor.relativePicardPresheaf A)
    (Scheme.fppfTopology.over S)
    (Functor.relativePicardSheaf A) (Functor.toRelativePicard A) (fun _ q r => Tensor.LineBundles.tensorClass q r)
    (fun {_ _} f q r => Tensor.LineBundles.tensorClass_pullback ((Functor.familySchemeFunctor A).map f.unop) q r) hq hr

variable [GrpObj A]

/-- Tensoring actual homogeneous line classes preserves homogeneity under every base change. -/
theorem tensor_isHomogeneous {T : Over S} {q r : (Functor.relativePicardPresheaf A).obj (op T)}
    (hq : Homogeneous.IsHomogeneous A T q) (hr : Homogeneous.IsHomogeneous A T r) :
    Homogeneous.IsHomogeneous A T (Tensor.LineBundles.tensorClass q r) := by
  intro U h a
  change (Functor.toRelativePicard A).app (op U)
      (Line.Bundles.LineBundleClass.pullback (Homogeneous.translation A a).left
        (Line.Bundles.LineBundleClass.pullback ((Functor.familySchemeFunctor A).map h) (Tensor.LineBundles.tensorClass q r))) =
    (Functor.toRelativePicard A).app (op U)
      (Line.Bundles.LineBundleClass.pullback ((Functor.familySchemeFunctor A).map h) (Tensor.LineBundles.tensorClass q r))
  erw [Tensor.LineBundles.tensorClass_pullback, Tensor.LineBundles.tensorClass_pullback]
  exact tensor_congr A (hq U h a) (hr U h a)

/-- The tensor product in the actual presheaf of homogeneous line classes. -/
def tensorHomogeneous {T : (Over S)ᵒᵖ}
    (q r : (Homogeneous.homogeneousPresheaf A).obj T) : (Homogeneous.homogeneousPresheaf A).obj T :=
  ⟨Tensor.LineBundles.tensorClass q.val r.val, tensor_isHomogeneous A q.property r.property⟩

/-- This presheaf product is natural in every test scheme. -/
theorem tensorHomogeneous_natural {T U : (Over S)ᵒᵖ} (h : T ⟶ U)
    (q r : (Homogeneous.homogeneousPresheaf A).obj T) :
    (Homogeneous.homogeneousPresheaf A).map h (tensorHomogeneous A q r) =
      tensorHomogeneous A ((Homogeneous.homogeneousPresheaf A).map h q) ((Homogeneous.homogeneousPresheaf A).map h r) := by
  apply Subtype.ext
  exact Tensor.LineBundles.tensorClass_pullback ((Functor.familySchemeFunctor A).map h.unop) q.val r.val

/-- Equality after homogeneous Picard sheafification is preserved by tensoring. -/
theorem tensorHomogeneous_congr {T : Over S} {q q' r r' : (Homogeneous.homogeneousPresheaf A).obj (op T)}
    (hq : (toSheafify (Scheme.fppfTopology.over S) (Homogeneous.homogeneousPresheaf A)).app (op T) q =
      (toSheafify (Scheme.fppfTopology.over S) (Homogeneous.homogeneousPresheaf A)).app (op T) q')
    (hr : (toSheafify (Scheme.fppfTopology.over S) (Homogeneous.homogeneousPresheaf A)).app (op T) r =
      (toSheafify (Scheme.fppfTopology.over S) (Homogeneous.homogeneousPresheaf A)).app (op T) r') :
    (toSheafify (Scheme.fppfTopology.over S) (Homogeneous.homogeneousPresheaf A)).app (op T)
        (tensorHomogeneous A q r) =
      (toSheafify (Scheme.fppfTopology.over S) (Homogeneous.homogeneousPresheaf A)).app (op T)
        (tensorHomogeneous A q' r') := by
  have hi : Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S)
      (toSheafify (Scheme.fppfTopology.over S) (Homogeneous.homogeneousPresheaf A)) :=
    Presheaf.isLocallyInjective_toSheafify' (Scheme.fppfTopology.over S) (Homogeneous.homogeneousPresheaf A)
  exact @SheafifiedBinaryCongruence.binary_congr (Over S) _
    (Scheme.fppfTopology.over S) (Homogeneous.homogeneousPresheaf A)
    (Homogeneous.homogeneousSheaf A) (toSheafify (Scheme.fppfTopology.over S) (Homogeneous.homogeneousPresheaf A))
    hi (fun _ q r => tensorHomogeneous A q r) (fun {_ _} f q r => tensorHomogeneous_natural A f q r)
    (op T) q q' r r' hq hr

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.TensorCongruence
