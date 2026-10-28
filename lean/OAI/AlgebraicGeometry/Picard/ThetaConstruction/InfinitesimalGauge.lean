import OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntegralDualLe
import OAI.RepresentationTheory.Theta.Geometric.InfinitesimalPolarizationGauge
import Mathlib.RingTheory.DualNumber

/-! # Infinitesimal Gauge -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction

noncomputable section

/-! Infinitesimal holomorphic gauges for the original ThetaConstruction Riemann form
have zero translation direction, by its actual nondegenerate pairing. -/

section
open OAI.RepresentationTheory.Theta.Geometric.InfinitesimalPolarizationGauge

variable {dim : ℕ} {E : DefinitionsIntegral.IntegralMatrix dim} (T : DefinitionsIntegral.MarkedPolarizedTorus dim E)

theorem DefinitionsIntegral.MarkedPolarizedTorus.infinitesimalGauge_eq_zero (a : DefinitionsIntegral.Tangent dim) (f : DefinitionsIntegral.Tangent dim → ℂ)
    (hf : Differentiable ℂ f)
    (htrans : ∀ (l : T.lattice) w,
      f (w + l.val) + (Real.pi : ℂ) * T.riemannForm l.val a = f w) : a = 0 := by
  let : CompactSpace ((DefinitionsIntegral.Tangent dim) ⧸ T.lattice) := T.compact
  have hs : Submodule.span ℝ (T.lattice : Set (DefinitionsIntegral.Tangent dim)) = ⊤ := by
    let : CompactSpace ((DefinitionsIntegral.Tangent dim) ⧸ T.lattice.toIntSubmodule.toAddSubgroup) := T.compact
    exact RepresentationTheory.Theta.Geometric.CompactLattice.span_top_of_compact_quotient T.lattice.toIntSubmodule
  have hlin : T.imaginaryForm a = 0 := by
    apply LinearMap.ext_on hs
    intro l hl
    exact RepresentationTheory.Theta.Geometric.InfinitesimalPolarizationGauge.infinitesimalPolarizationGauge_pairing_zero T.lattice T.riemannForm T.hermitian
      a f hf htrans ⟨l, hl⟩
  exact T.imaginaryForm_nondegenerate.1 a (fun v => DFunLike.congr_fun hlin v)

theorem DefinitionsIntegral.MarkedPolarizedTorus.dualNumberGauge_eq_zero (a : DefinitionsIntegral.Tangent dim) (c : DefinitionsIntegral.Tangent dim → DualNumber ℂ)
    (hc : Differentiable ℂ (fun w => (c w).snd)) (hfirst : ∀ w, (c w).fst = 1)
    (htrans : ∀ (l : T.lattice) w, c (w + l.val) *
      (1 + TrivSqZeroExt.inr ((Real.pi : ℂ) * T.riemannForm l.val a)) = c w) : a = 0 := by
  apply T.infinitesimalGauge_eq_zero a (fun w => (c w).snd) hc
  intro l w
  have H := congrArg TrivSqZeroExt.snd (htrans l w)
  simpa only [DualNumber.snd_mul, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_add,
    TrivSqZeroExt.snd_one, TrivSqZeroExt.fst_one, TrivSqZeroExt.snd_inr,
    TrivSqZeroExt.fst_inr, zero_add, add_zero, hfirst, one_mul, mul_one, add_comm] using H

end

namespace InfinitesimalGauge.Geometric.MarkedPolarizedTorus

end InfinitesimalGauge.Geometric.MarkedPolarizedTorus

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction
