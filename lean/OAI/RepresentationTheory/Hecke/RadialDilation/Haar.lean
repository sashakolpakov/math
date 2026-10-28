import OAI.RepresentationTheory.Hecke.RadialDilation.Mem

/-! # Haar -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.Haar.Realization

noncomputable section

/-! The Haar modulus on Q_q, with its arithmetic normalization. -/

open scoped Classical Pointwise ENNReal
open _root_.MeasureTheory

variable (q : ℕ) [Fact q.Prime]

local instance c410Haar_localInst1 : MeasurableSpace ℚ_[q] := borel ℚ_[q]
local instance c410Haar_localInst2 : BorelSpace ℚ_[q] := ⟨rfl⟩
local instance c410Haar_localInst3 : MeasurableSpace ℤ_[q] :=
  inferInstanceAs (MeasurableSpace {x : ℚ_[q] // ‖x‖ ≤ 1})
local instance c410Haar_localInst4 : BorelSpace ℤ_[q] :=
  inferInstanceAs (BorelSpace {x : ℚ_[q] // ‖x‖ ≤ 1})

def integralBall : Set ℚ_[q] := {x | ‖x‖ ≤ 1}
def smallIntegralBall : Set ℚ_[q] := {x | ‖x‖ ≤ (q : ℝ)⁻¹}

theorem integralBall_compact : IsCompact (integralBall q) := by
  simpa [integralBall, Metric.closedBall, dist_eq_norm] using
    isCompact_closedBall (0 : ℚ_[q]) (1 : ℝ)

theorem integralBall_measure_pos :
    0 < (Measure.addHaar : Measure ℚ_[q]) (integralBall q) := by
  simpa [integralBall, Metric.closedBall, dist_eq_norm] using
    Metric.measure_closedBall_pos (Measure.addHaar : Measure ℚ_[q]) 0 zero_lt_one

theorem integralBall_measure_ne_top :
    (Measure.addHaar : Measure ℚ_[q]) (integralBall q) ≠ ⊤ :=
  (integralBall_compact q).measure_lt_top.ne

def residueKernel : AddSubgroup ℤ_[q] :=
  (PadicInt.toZMod : ℤ_[q] →+* ZMod q).toAddMonoidHom.ker

theorem residueKernel_iff (x : ℤ_[q]) :
    x ∈ residueKernel q ↔ ‖(x : ℚ_[q])‖ ≤ (q : ℝ)⁻¹ := by
  change PadicInt.toZMod x = 0 ↔ _
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p]
  have h := PadicInt.norm_le_pow_iff_mem_span_pow x 1
  simpa using h.symm

theorem residueKernel_measurable : MeasurableSet (residueKernel q : Set ℤ_[q]) := by
  have he : (residueKernel q : Set ℤ_[q]) =
      {x : ℤ_[q] | ‖(x : ℚ_[q])‖ ≤ (q : ℝ)⁻¹} := by
    ext x
    exact residueKernel_iff q x
  rw [he]
  have hc : Continuous (fun x : ℤ_[q] => ‖(x : ℚ_[q])‖) :=
    PadicInt.isOpenEmbedding_coe.continuous.norm
  exact (isClosed_le hc continuous_const).measurableSet

theorem residueKernel_index : (residueKernel q).index = q := by
  rw [residueKernel, AddSubgroup.index_ker]
  have hr : (PadicInt.toZMod : ℤ_[q] →+* ZMod q).toAddMonoidHom.range = ⊤ :=
    AddMonoidHom.range_eq_top.mpr (ZMod.ringHom_surjective PadicInt.toZMod)
  rw [hr]
  simp [Nat.card_eq_fintype_card]

theorem smallIntegralBall_measure :
    (q : ℝ≥0∞) * (Measure.addHaar : Measure ℚ_[q]) (smallIntegralBall q) =
      (Measure.addHaar : Measure ℚ_[q]) (integralBall q) := by
  let μ : Measure ℚ_[q] := Measure.addHaar
  let e : ℤ_[q] →+ ℚ_[q] := PadicInt.Coe.ringHom.toAddMonoidHom
  let ν : Measure ℤ_[q] := μ.comap e
  have he : Topology.IsOpenEmbedding e := PadicInt.isOpenEmbedding_coe
  let : ν.IsAddHaarMeasure := Measure.IsAddHaarMeasure.comap (mH := inferInstance) μ he
  let : (residueKernel q).FiniteIndex :=
    AddSubgroup.finiteIndex_ker (PadicInt.toZMod : ℤ_[q] →+* ZMod q).toAddMonoidHom
  have h := (residueKernel q).index_mul_measure (residueKernel_measurable q) ν
  rw [residueKernel_index] at h
  have he0 : e '' (Set.univ : Set ℤ_[q]) = integralBall q := by
    ext x
    exact ⟨fun ⟨a, _, hx⟩ => hx ▸ a.property,
      fun hx => ⟨⟨x, hx⟩, Set.mem_univ _, rfl⟩⟩
  have he1 : e '' (residueKernel q : Set ℤ_[q]) = smallIntegralBall q := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (residueKernel_iff q a).mp ha
    · intro hx
      have hq : 1 ≤ (q : ℝ) := by exact_mod_cast (Fact.out : q.Prime).one_le
      have hx1 : ‖x‖ ≤ 1 := hx.trans (inv_le_one_of_one_le₀ hq)
      exact ⟨⟨x, hx1⟩, (residueKernel_iff q ⟨x, hx1⟩).mpr hx, rfl⟩
  change (q : ℝ≥0∞) * μ.comap e (residueKernel q) = μ.comap e Set.univ at h
  rw [he.measurableEmbedding.comap_apply, he.measurableEmbedding.comap_apply, he0, he1] at h
  exact h

theorem unit_smul_integralBall (a : ℚ_[q]ˣ) (ha : ‖(a : ℚ_[q])‖ = 1) :
    a • integralBall q = integralBall q := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change ‖(a : ℚ_[q]) * y‖ ≤ 1
    change ‖y‖ ≤ 1 at hy
    simpa [norm_mul, ha] using hy
  · intro hx
    refine ⟨(a : ℚ_[q])⁻¹ * x, ?_, ?_⟩
    swap
    · change (a : ℚ_[q]) * ((a : ℚ_[q])⁻¹ * x) = x
      rw [mul_inv_cancel_left₀ a.ne_zero]
    change ‖(a : ℚ_[q])⁻¹ * x‖ ≤ 1
    change ‖x‖ ≤ 1 at hx
    simpa [norm_mul, norm_inv, ha] using hx

theorem haarModulus_unit_norm_one (a : ℚ_[q]ˣ) (ha : ‖(a : ℚ_[q])‖ = 1) :
    Weil.Local.FunctionsMetaplectic.Construction.localModulus ℚ_[q] a = 1 := by
  have h := distribHaarChar_mul (Measure.addHaar : Measure ℚ_[q]) a (integralBall q)
  rw [unit_smul_integralBall q a ha] at h
  have hn := integralBall_measure_pos q
  have ht := integralBall_measure_ne_top q
  have he : (distribHaarChar ℚ_[q] a : ℝ≥0∞) = 1 := by
    apply (ENNReal.mul_left_inj hn.ne' ht).mp
    simpa using h
  change (distribHaarChar ℚ_[q] a : ℝ) = 1
  exact_mod_cast he

theorem scalar_smul_integralBall (a : ℚ_[q]ˣ) :
    a • integralBall q = {x : ℚ_[q] | ‖x‖ ≤ ‖(a : ℚ_[q])‖} := by
  have ha : 0 < ‖(a : ℚ_[q])‖ := norm_pos_iff.mpr a.ne_zero
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change ‖(a : ℚ_[q]) * y‖ ≤ ‖(a : ℚ_[q])‖
    rw [norm_mul]
    exact mul_le_of_le_one_right ha.le hy
  · intro hx
    refine ⟨(a : ℚ_[q])⁻¹ * x, ?_, ?_⟩
    · change ‖(a : ℚ_[q])⁻¹ * x‖ ≤ 1
      rw [norm_mul, norm_inv, mul_comm, ← div_eq_mul_inv]
      exact (div_le_one ha).mpr hx
    · change (a : ℚ_[q]) * ((a : ℚ_[q])⁻¹ * x) = x
      rw [mul_inv_cancel_left₀ a.ne_zero]

def uniformizerUnit : ℚ_[q]ˣ :=
  Units.mk0 (q : ℚ_[q]) (by exact_mod_cast (Fact.out : q.Prime).ne_zero)

theorem haarModulus_uniformizer :
    Weil.Local.FunctionsMetaplectic.Construction.localModulus ℚ_[q] (uniformizerUnit q) = (q : ℝ)⁻¹ := by
  let μ : Measure ℚ_[q] := Measure.addHaar
  have h := distribHaarChar_mul μ (uniformizerUnit q) (integralBall q)
  rw [scalar_smul_integralBall] at h
  change (distribHaarChar ℚ_[q] (uniformizerUnit q) : ℝ≥0∞) * μ (integralBall q) =
    μ {x : ℚ_[q] | ‖x‖ ≤ ‖(q : ℚ_[q])‖} at h
  rw [Padic.norm_p] at h
  have hm := smallIntegralBall_measure q
  have hreal := congrArg ENNReal.toReal h
  have hmreal := congrArg ENNReal.toReal hm
  simp only [ENNReal.toReal_mul, ENNReal.coe_toReal] at hreal
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast] at hmreal
  change (distribHaarChar ℚ_[q] (uniformizerUnit q) : ℝ) *
    (μ (integralBall q)).toReal = (μ (smallIntegralBall q)).toReal at hreal
  have hv : (μ (integralBall q)).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨(integralBall_measure_pos q).ne', integralBall_measure_ne_top q⟩
  have hc : (q : ℝ) * (distribHaarChar ℚ_[q] (uniformizerUnit q) : ℝ) = 1 := by
    apply mul_right_cancel₀ hv
    calc
      ((q : ℝ) * (distribHaarChar ℚ_[q] (uniformizerUnit q) : ℝ)) *
          (μ (integralBall q)).toReal =
          (q : ℝ) * ((distribHaarChar ℚ_[q] (uniformizerUnit q) : ℝ) *
            (μ (integralBall q)).toReal) := by ring
      _ = (q : ℝ) * (μ (smallIntegralBall q)).toReal := by rw [hreal]
      _ = (μ (integralBall q)).toReal := hmreal
      _ = 1 * (μ (integralBall q)).toReal := by ring
  change (distribHaarChar ℚ_[q] (uniformizerUnit q) : ℝ) = (q : ℝ)⁻¹
  exact eq_inv_of_mul_eq_one_right hc

theorem haarModulus_of_norm (a : ℚ_[q]ˣ) (M : ℕ)
    (ha : ‖(a : ℚ_[q])‖ = (q : ℝ) ^ (-(M : ℤ))) :
    Weil.Local.FunctionsMetaplectic.Construction.localModulus ℚ_[q] a = ‖(a : ℚ_[q])‖ := by
  let u := a * ((uniformizerUnit q) ^ M)⁻¹
  have hnorm : ‖(u : ℚ_[q])‖ = 1 := by
    have hq : (q : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
    simp [u, uniformizerUnit, norm_mul, norm_inv, ha, hq]
  have he : u * (uniformizerUnit q) ^ M = a := by simp [u]
  have hu := haarModulus_unit_norm_one q u hnorm
  have hp := haarModulus_uniformizer q
  rw [← he, Weil.Local.FunctionsMetaplectic.Construction.localModulus_mul, hu, one_mul]
  have hpow : Weil.Local.FunctionsMetaplectic.Construction.localModulus ℚ_[q] ((uniformizerUnit q) ^ M) =
      (Weil.Local.FunctionsMetaplectic.Construction.localModulus ℚ_[q] (uniformizerUnit q)) ^ M := by
    simp [Weil.Local.FunctionsMetaplectic.Construction.localModulus, map_pow]
  rw [hpow, hp, he, ha]
  simp [zpow_neg, inv_pow]

end

end OAI.RepresentationTheory.Hecke.RadialDilation.Haar.Realization
