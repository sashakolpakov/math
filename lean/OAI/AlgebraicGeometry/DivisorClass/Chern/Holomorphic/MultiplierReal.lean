import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Multiplier
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSmooth.MultiplierIdentities

/-! # Multiplier Real -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.MultiplierReal

noncomputable section

section

/-! Original bounded bundle multipliers absorb inner cutoffs and sum to the identity for a genuine finite partition. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u) (n : ℕ)

theorem holomorphicMetricL2Multiplier_absorb (f g : V.analyticSpace → ℂ)
    (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ g)
    (hfg : ∀ x ∈ tsupport f, g x = 1) (v : IntegralPairZero.HolomorphicFormL2With V h n) :
    Multiplier.holomorphicMetricL2Multiplier V h n f hf (Multiplier.holomorphicMetricL2Multiplier V h n g hg v) =
      Multiplier.holomorphicMetricL2Multiplier V h n f hf v :=
  congrFun ((IntegralPairZero.holomorphicFormL2WithInclusion_dense V h n).equalizer
    ((Multiplier.holomorphicMetricL2Multiplier V h n f hf).continuous.comp (Multiplier.holomorphicMetricL2Multiplier V h n g hg).continuous) (Multiplier.holomorphicMetricL2Multiplier V h n f hf).continuous
    (funext (fun a =>
      Eq.trans (congrArg (Multiplier.holomorphicMetricL2Multiplier V h n f hf) (Multiplier.holomorphicMetricL2Multiplier_on_smooth V h n g hg a))
        (Eq.trans (Multiplier.holomorphicMetricL2Multiplier_on_smooth V h n f hf (SupportedForms.holomorphicLineSmoothMul u ⊤ n g hg a))
          (Eq.trans (congrArg (IntegralPairZero.holomorphicFormL2WithInclusion V h n) (HolomorphicSmooth.MultiplierIdentities.holomorphicLineSmoothMul_absorb V n f g hf hg hfg a))
            (Multiplier.holomorphicMetricL2Multiplier_on_smooth V h n f hf a).symm))))) v

theorem holomorphicMetricL2Multiplier_partition {ι : Type*} [Fintype ι]
    (f : ι → V.analyticSpace → ℂ)
    (hf : ∀ i, ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ (f i))
    (hsum : ∀ x, ∑ i, f i x = 1) (v : IntegralPairZero.HolomorphicFormL2With V h n) :
    ∑ i, Multiplier.holomorphicMetricL2Multiplier V h n (f i) (hf i) v = v := by
  have hclosed : IsClosed {w : IntegralPairZero.HolomorphicFormL2With V h n |
      (∑ i, Multiplier.holomorphicMetricL2Multiplier V h n (f i) (hf i) w) = w} :=
    isClosed_eq (continuous_finsetSum _ (fun i _ => (Multiplier.holomorphicMetricL2Multiplier V h n (f i) (hf i)).continuous))
      continuous_id
  refine (IntegralPairZero.holomorphicFormL2WithInclusion_dense V h n).induction_on v hclosed (fun a => ?_)
  change (∑ i, Multiplier.holomorphicMetricL2Multiplier V h n (f i) (hf i) (IntegralPairZero.holomorphicFormL2WithInclusion V h n a)) = _
  simp only [Multiplier.holomorphicMetricL2Multiplier_on_smooth]
  rw [← map_sum, HolomorphicSmooth.MultiplierIdentities.holomorphicLineSmoothMul_partition V n f hf hsum a]

end

section

/-! Real original scalar cutoffs and their exact finite partition on the actual bundle Hilbert completion. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u) (n : ℕ)

def holomorphicMetricRealL2Multiplier (f : V.analyticSpace → ℝ)
    (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℝ) ∞ f) :
    IntegralPairZero.HolomorphicFormL2With V h n →L[ℂ] IntegralPairZero.HolomorphicFormL2With V h n :=
  Multiplier.holomorphicMetricL2Multiplier V h n (fun x => (f x : ℂ)) (Complex.ofRealCLM.contDiff.contMDiff.comp hf)

theorem holomorphicMetricRealL2Multiplier_partition {ι : Type*} [Fintype ι]
    (f : ι → V.analyticSpace → ℝ)
    (hf : ∀ i, ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℝ) ∞ (f i))
    (hsum : ∀ x, ∑ i, f i x = 1) (v : IntegralPairZero.HolomorphicFormL2With V h n) :
    ∑ i, holomorphicMetricRealL2Multiplier V h n (f i) (hf i) v = v :=
  holomorphicMetricL2Multiplier_partition V h n (fun i x => (f i x : ℂ))
    (fun i => Complex.ofRealCLM.contDiff.contMDiff.comp (hf i))
    (fun x => by rw [← Complex.ofReal_sum, hsum x, Complex.ofReal_one]) v

end

/-! Exact scalar-function equality transports original bounded multipliers, and real scalar support survives complexification. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem realScalar_complex_tsupport {X : Type*} [TopologicalSpace X] (f : X → ℝ) :
    tsupport (fun x => (f x : ℂ)) = tsupport f := by
  apply congrArg closure
  ext x
  simp only [Function.mem_support]
  exact not_congr Complex.ofReal_eq_zero

theorem holomorphicMetricL2Multiplier_congr (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u) (n : ℕ)
    (f g : V.analyticSpace → ℂ)
    (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ g)
    (hfg : f = g) (v : IntegralPairZero.HolomorphicFormL2With V h n) :
    Multiplier.holomorphicMetricL2Multiplier V h n f hf v = Multiplier.holomorphicMetricL2Multiplier V h n g hg v := by
  subst g
  rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.MultiplierReal
