import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.WedgeDerivativeTerms
import OAI.NumberTheory.PadicHodge.IntegralComparison.Open.SmoothProducts

/-! # Manifold Wedge Leibniz -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ManifoldWedgeLeibniz.Smooth

noncomputable section

/-! The graded product rule for genuine manifold forms and the
original forms on open subsets. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {p q : ℕ}

theorem manifold_d_wedge (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M p) (b : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M q) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge a b) =
      AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldDegreeCast (by omega) (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a) b) +
        (-1 : ℤ) ^ p • AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldDegreeCast (by omega) (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge a (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d b)) := by
  rw [← Int.cast_smul_eq_zsmul ℂ]
  apply AlgebraicGeometry.Comparison.Betti.Smooth.Wedge.eq_of_inChart
  intro e he y hy
  rw [Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_inChart _ e he hy]
  change extDeriv ((AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldWedge a.val b.val).inChart e) y =
    ((AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldDegreeCast (by omega) (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldWedge (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a).val b.val)) +
      (Int.cast ((-1 : ℤ) ^ p) : ℂ) •
        AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldDegreeCast (by omega) (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldWedge a.val (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d b).val)).inChart e y
  rw [Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_add, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_smul]
  change extDeriv ((AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldWedge a.val b.val).inChart e) y =
    (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldDegreeCast (by omega) (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldWedge (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a).val b.val)).inChart e y +
      (Int.cast ((-1 : ℤ) ^ p) : ℂ) •
        (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldDegreeCast (by omega) (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldWedge a.val (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d b).val)).inChart e y
  rw [AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldDegreeCast_inChart, AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldDegreeCast_inChart,
    AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldWedge_inChart, AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldWedge_inChart, AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldWedge_inChart]
  dsimp only
  rw [Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_inChart a e he hy, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_inChart b e he hy]
  simpa only [Int.cast_pow, Int.cast_neg, Int.cast_one, ← Int.cast_smul_eq_zsmul ℂ] using
    Smooth.WedgeDerivativeTerms.Leibniz.extDeriv_wedge (a.val.inChart e) (b.val.inChart e) y
      ((Analysis.DifferentialForms.Manifold.Derivative.smoothForm_contDiffAt_inChart a.smooth e he hy).of_le (by simp))
      ((Analysis.DifferentialForms.Manifold.Derivative.smoothForm_contDiffAt_inChart b.smooth e he hy).of_le (by simp))

def openDegreeCast (U : Opens M) {m n : ℕ} (h : m = n) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U m ≃ₗ[ℂ] Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n :=
  h ▸ LinearEquiv.refl ℂ (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U m)

theorem intrinsic_openDegreeCast (U : Opens M) {m n : ℕ} (h : m = n)
    (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U m) :
    Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U n (openDegreeCast U h a) =
      AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldDegreeCast h (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U m a) := by
  subst n
  rfl

theorem intrinsic_zsmul (U : Opens M) (n : ℕ) (z : ℤ) (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n) :
    Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U n (z • a) = z • Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U n a := by
  exact map_zsmul (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U n).toAddEquiv z a

theorem open_d_wedge (U : Opens M) (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U p) (b : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U q) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (Open.SmoothProducts.wedge U p q a b) =
      openDegreeCast U (by omega) (Open.SmoothProducts.wedge U (p + 1) q (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d a) b) +
        (-1 : ℤ) ^ p • openDegreeCast U (by omega)
          (Open.SmoothProducts.wedge U p (q + 1) a (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d b)) := by
  apply (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U (p + q + 1)).injective
  rw [map_add, intrinsic_zsmul,
    intrinsic_openDegreeCast, intrinsic_openDegreeCast,
    ← Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv_d, Open.SmoothProducts.intrinsic_wedge,
    Open.SmoothProducts.intrinsic_wedge, Open.SmoothProducts.intrinsic_wedge,
    ← Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv_d, ← Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv_d]
  exact manifold_d_wedge _ _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ManifoldWedgeLeibniz.Smooth
