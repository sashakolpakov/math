import OAI.RepresentationTheory.Weil.AdelicSplitting.UniformPoisson
import OAI.RepresentationTheory.Weil.AdelicSplitting.FourierRelations

/-! # Exact Fourier -/

namespace OAI.RepresentationTheory.Theta.Adelic.ExactFourier

noncomputable section

/-! Exact Poisson invariance follows from the proved positive multiplier,
a common lattice of periods, and the actual Fourier fourth-power relation. -/

open scoped Classical _root_.NumberField
open _root_.NumberField IsDedekindDomain _root_.MeasureTheory

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

theorem common_finite_period {I : Type*} [Fintype I]
    (f : I → Weil.AdelicSplitting.RestrictedTestFamilies.Construction.RestrictedTestFamily F N) :
    ∃ M : ℕ, ∃ hM : 0 < M, ∀ i : I,
      ∀ u ∈ Weil.AdelicSplitting.FiniteLattices.Construction.finiteAdelicPositionLattice (ι := Fin N) (M : F) (by exact_mod_cast hM.ne'),
        ∀ x, (f i).finiteValue F N (u + x) = (f i).finiteValue F N x := by
  let U : OpenAddSubgroup (Fin N → Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :=
    { toAddSubgroup := ⨅ i : I, Weil.AdelicSplitting.FiniteLattices.Construction.functionTranslationStabilizer ((f i).finiteValue F N)
      isOpen' := by
        have hi := isOpen_iInter_of_finite (fun i : I =>
          Weil.AdelicSplitting.FiniteLattices.Construction.functionTranslationStabilizer_isOpen ((f i).finiteValue F N)
            ((f i).finiteValue_locallyConstant F N) ((f i).finiteValue_compactSupport F N))
        rw [← AddSubgroup.coe_iInf] at hi
        exact hi }
  obtain ⟨M, hM, h⟩ := Weil.AdelicSplitting.FiniteLattices.Construction.finitePosition_open_integer_multiple F U
  refine ⟨M, hM, fun i u hu x => ?_⟩
  obtain ⟨v, hv, rfl⟩ := hu
  change (f i).finiteValue F N (Weil.AdelicSplitting.FiniteLattices.Construction.finitePositionScale (M : F) v + x) = _
  rw [Weil.AdelicSplitting.FiniteLattices.Construction.finitePositionScale_natCast]
  have hh := h (fun j => ⟨v j, hv j⟩)
  exact (AddSubgroup.mem_iInf.mp hh i) x

local instance (v : HeightOneSpectrum (𝓞 F)) : MeasurableSpace (v.adicCompletion F) :=
  borel (v.adicCompletion F)
local instance (v : HeightOneSpectrum (𝓞 F)) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
local instance (v : InfinitePlace F) : MeasurableSpace v.Completion := borel v.Completion
local instance (v : InfinitePlace F) : BorelSpace v.Completion := ⟨rfl⟩

variable (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ) (hu : ∀ x, ‖ψ x‖ = 1)
variable (hp : ∀ q : F, ψ (algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) q) = 1)
variable (hn : ∀ v : InfinitePlace F, ∃ t : v.Completion, Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ (.inl v) t ≠ 1)
variable (hμf : ∀ v : HeightOneSpectrum (𝓞 F),
  (Weil.Local.FunctionsMetaplectic.Construction.positionMeasure (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) N (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ (.inr v))).IsAddHaarMeasure)
variable (hμa : ∀ v : InfinitePlace F,
  (Weil.Local.FunctionsMetaplectic.Construction.positionMeasure (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl v)) N (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ (.inl v))).IsAddHaarMeasure)

include hc hu hp hn hμf hμa in
theorem theta_fourier_exact (a : Weil.AdelicSplitting.Rational.Construction.RestrictedCover F N ψ) (ha : Weil.AdelicSplitting.Rational.Construction.IsRationalFourier F N ψ a)
    (hfourth : a ^ 4 = 1) (f : Weil.AdelicSplitting.RestrictedTestFamilies.Construction.RestrictedTestFamily F N) :
    (f.act F N ψ a).theta F N = f.theta F N := by
  let fₖ (i : Fin 4) : Weil.AdelicSplitting.RestrictedTestFamilies.Construction.RestrictedTestFamily F N := f.act F N ψ (a ^ i.val)
  obtain ⟨M, hM, hperiod⟩ := common_finite_period F N fₖ
  obtain ⟨c, hcpos, hct⟩ := Weil.AdelicSplitting.UniformPoisson.Construction.theta_fourier_uniform_period F N ψ hc hu hp hn hμf hμa a ha M hM
  have hstep (i : Fin 4) :
      (f.act F N ψ (a ^ (i.val + 1))).theta F N =
        (c : ℂ) * (f.act F N ψ (a ^ i.val)).theta F N := by
    have h := hct (fₖ i) (hperiod i)
    rw [← Weil.AdelicSplitting.RestrictedTestFamilies.Construction.RestrictedTestFamily.act_mul, ← pow_succ'] at h
    exact h
  have h0 := hstep 0
  have h1 := hstep 1
  have h2 := hstep 2
  have h3 := hstep 3
  norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, zero_add, pow_zero,
    pow_one, Weil.AdelicSplitting.RestrictedTestFamilies.Construction.RestrictedTestFamily.act_one] at h0 h1 h2 h3
  change (f.act F N ψ (a ^ 3)).theta F N = (c : ℂ) * (f.act F N ψ (a ^ 2)).theta F N at h2
  change (f.act F N ψ (a ^ 4)).theta F N = (c : ℂ) * (f.act F N ψ (a ^ 3)).theta F N at h3
  have he : f.theta F N = (c : ℂ) ^ 4 * f.theta F N := by
    calc
      f.theta F N = (f.act F N ψ (a ^ 4)).theta F N := by rw [hfourth, f.act_one F N ψ]
      _ = (c : ℂ) ^ 4 * f.theta F N := by rw [h3, h2, h1, h0]; ring
  by_cases hf : f.theta F N = 0
  · rw [h0, hf, mul_zero]
  · have hc4 : (c : ℂ) ^ 4 = 1 := by
      apply mul_right_cancel₀ hf
      rw [one_mul]
      exact he.symm
    have hr4 : c ^ 4 = 1 := by exact_mod_cast hc4
    have hceq : c = 1 := by nlinarith [sq_nonneg (c ^ 2 - 1), sq_nonneg (c - 1)]
    simpa only [hceq, Complex.ofReal_one, one_mul] using h0

end

end OAI.RepresentationTheory.Theta.Adelic.ExactFourier
