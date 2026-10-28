import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PolarizationFactor
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Lattice
import OAI.RepresentationTheory.Theta.Geometric.InfinitesimalPolarizationGauge
import Mathlib.RingTheory.DualNumber

/-! # Infinitesimal Gauge -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference

noncomputable section

/-! Infinitesimal holomorphic translation gauges for the exact reference
polarization have zero translation vector. The conclusion uses the
nondegenerate imaginary form on the original period space. -/

open OAI.RepresentationTheory.Theta.Geometric.InfinitesimalPolarizationGauge

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} (F : Fiber.ReferenceAnalyticFiber P z)

theorem Fiber.ReferenceAnalyticFiber.infinitesimalGauge_eq_zero (a : Fiber.ReferenceTangent s) (f : Fiber.ReferenceTangent s → ℂ)
    (hf : Differentiable ℂ f)
    (htrans : ∀ (l : P.lattice) w, f (w + F.latticeEmbedding l) +
      (Real.pi : ℂ) * F.form (F.latticeEmbedding l) a = f w) : a = 0 := by
  let : CompactSpace (Fiber.ReferenceTangent s ⧸ F.lattice) := F.compact
  have hshift (l : F.lattice) (w : Fiber.ReferenceTangent s) :
      f (w + l.val) + (Real.pi : ℂ) * F.form l.val a = f w := by
    have H := htrans (F.integralLatticeEquiv.symm l) w
    have hl := F.latticeEmbedding_symm l
    exact (congrArg (fun v : Fiber.ReferenceTangent s => f (w + v) + (Real.pi : ℂ) * F.form v a) hl).symm.trans H
  have hs : Submodule.span ℝ (F.lattice : Set (Fiber.ReferenceTangent s)) = ⊤ := by
    let : CompactSpace (Fiber.ReferenceTangent s ⧸ F.lattice.toIntSubmodule.toAddSubgroup) := F.compact
    exact RepresentationTheory.Theta.Geometric.CompactLattice.span_top_of_compact_quotient F.lattice.toIntSubmodule
  have hlin : F.imaginaryForm a = 0 := by
    apply LinearMap.ext_on hs
    intro l hl
    exact RepresentationTheory.Theta.Geometric.InfinitesimalPolarizationGauge.infinitesimalPolarizationGauge_pairing_zero F.lattice F.form F.hermitian a f hf hshift ⟨l, hl⟩
  exact F.imaginaryForm_nondegenerate.1 a (fun v => DFunLike.congr_fun hlin v)

theorem Fiber.ReferenceAnalyticFiber.dualNumberGauge_eq_zero (a : Fiber.ReferenceTangent s) (c : Fiber.ReferenceTangent s → DualNumber ℂ)
    (hc : Differentiable ℂ (fun w => (c w).snd)) (hfirst : ∀ w, (c w).fst = 1)
    (htrans : ∀ (l : P.lattice) w, c (w + F.latticeEmbedding l) *
      (1 + TrivSqZeroExt.inr ((Real.pi : ℂ) * F.form (F.latticeEmbedding l) a)) = c w) : a = 0 := by
  apply F.infinitesimalGauge_eq_zero a (fun w => (c w).snd) hc
  intro l w
  have H := congrArg TrivSqZeroExt.snd (htrans l w)
  simpa only [DualNumber.snd_mul, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_add,
    TrivSqZeroExt.snd_one, TrivSqZeroExt.fst_one, TrivSqZeroExt.snd_inr,
    TrivSqZeroExt.fst_inr, zero_add, add_zero, hfirst, one_mul, mul_one, add_comm] using H

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference
