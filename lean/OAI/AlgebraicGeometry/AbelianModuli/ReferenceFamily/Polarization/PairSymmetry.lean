import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.BiextensionPairFormula
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.LineBundleDual

/-! # Pair Symmetry -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarization.PairSymmetry

noncomputable section

/-! The original ample polarization formula forces symmetry of
its actual Poincare pairing on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {g N : ℕ} {δ : Fin g → ℕ} (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)

theorem polarizationPair_class_symm (T : Over Foundations.Scheme.ProjectiveSpace.complexBase) (a b : T ⟶ A.abelian.scheme) :
    A.dual.poincarePairClass T (a ≫ A.polarization.isogeny.hom) b =
      A.dual.poincarePairClass T (b ≫ A.polarization.isogeny.hom) a := by
  let x := HilbertConstruction.Line.Bundles.LineBundle.classOf ((Intrinsic.ChernPairing.polarizationLineBundle A).pullback a.left)
  let y := HilbertConstruction.Line.Bundles.LineBundle.classOf ((Intrinsic.ChernPairing.polarizationLineBundle A).pullback b.left)
  have h : A.dual.poincarePairClass T (a ≫ A.polarization.isogeny.hom) b * (x * y) =
      A.dual.poincarePairClass T (b ≫ A.polarization.isogeny.hom) a * (x * y) := by
    calc
      _ = HilbertConstruction.Line.Bundles.LineBundle.classOf ((Intrinsic.ChernPairing.polarizationLineBundle A).pullback (a * b).left) :=
        (mul_assoc _ x y).symm.trans (BiextensionPairFormula.polarizationPair_tensor_formula A T a b)
      _ = HilbertConstruction.Line.Bundles.LineBundle.classOf ((Intrinsic.ChernPairing.polarizationLineBundle A).pullback (b * a).left) :=
        congrArg (fun f : T ⟶ A.abelian.scheme => HilbertConstruction.Line.Bundles.LineBundle.classOf ((Intrinsic.ChernPairing.polarizationLineBundle A).pullback f.left))
          (mul_comm a b)
      _ = A.dual.poincarePairClass T (b ≫ A.polarization.isogeny.hom) a * (y * x) :=
        (BiextensionPairFormula.polarizationPair_tensor_formula A T b a).symm.trans (mul_assoc _ y x)
      _ = _ := congrArg (fun z => A.dual.poincarePairClass T (b ≫ A.polarization.isogeny.hom) a * z) (mul_comm y x)
  exact mul_right_cancel h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarization.PairSymmetry
