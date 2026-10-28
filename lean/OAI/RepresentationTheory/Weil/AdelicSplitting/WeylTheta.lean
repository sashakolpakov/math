import OAI.RepresentationTheory.Weil.AdelicSplitting.WeylFamilies
import OAI.RepresentationTheory.Weil.AdelicSplitting.CorrelationTheta
import OAI.RepresentationTheory.Weil.AdelicSplitting.UniformPoisson

/-! # Weyl Theta -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting

noncomputable section

/-! Poisson summation identifies the rational theta sum of Weyl coefficients
with a positive multiple of the product of the original theta sums. -/

open _root_.MeasureTheory
open scoped Classical _root_.NumberField ComplexConjugate

local instance WeylTheta.Construction.weylThetaFiniteMeasurable (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : MeasurableSpace (v.adicCompletion F) := borel (v.adicCompletion F)
local instance WeylTheta.Construction.weylThetaFiniteBorel (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
local instance WeylTheta.Construction.weylThetaInfiniteMeasurable (F : Type) [Field F]
    (v : NumberField.InfinitePlace F) : MeasurableSpace v.Completion := borel v.Completion
local instance WeylTheta.Construction.weylThetaInfiniteBorel (F : Type) [Field F]
    (v : NumberField.InfinitePlace F) : BorelSpace v.Completion := ⟨rfl⟩

theorem WeylTheta.Construction.midpointRationalEquiv_local {F k : Type} [Field F] [CharZero F] [NormedField k]
    (N : ℕ) (e : F →+* k) (q p : Fin N → F) :
    (PhaseMeasure.Construction.phaseCoordinates k N).symm (fun i => e (WeylMidpoint.Construction.midpointRationalEquiv F N (q, p) i)) =
      Sum.elim (2 • fun i => e (q i)) (-(fun i => e (p i))) := by
  funext j
  cases j with
  | inl i =>
      change e (Sum.elim (fun j => 2 * q j) (fun j => -p j)
        (finSumFinEquiv.symm (finSumFinEquiv (.inl i)))) = (2 • (fun i => e (q i))) i
      simp only [Equiv.symm_apply_apply, Sum.elim_inl, Pi.smul_apply, two_smul, two_mul, map_add]
  | inr i =>
      change e (Sum.elim (fun j => 2 * q j) (fun j => -p j)
        (finSumFinEquiv.symm (finSumFinEquiv (.inr i)))) = -e (p i)
      simp only [Equiv.symm_apply_apply, Sum.elim_inr, map_neg]

variable (F : Type) [Field F] [NumberField F] (N : ℕ)
variable (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1)
variable (hn : ∀ v : ArchimedeanAdeles.Construction.Places F, ∃ t : ArchimedeanAdeles.Construction.Completion F v, Characters.Construction.localAdditiveCharacter F ψ v t ≠ 1)
variable (hμ : ∀ v : ArchimedeanAdeles.Construction.Places F,
  (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F v) N (Characters.Construction.localAdditiveCharacter F ψ v)).IsAddHaarMeasure)
variable (a : Rational.Construction.RestrictedCover F N ψ) (ha : Rational.Construction.IsRationalFourier F N ψ a)

theorem RestrictedTestFamilies.Construction.RestrictedTestFamily.weylCoefficients_value_midpoint (f h : RestrictedTestFamilies.Construction.RestrictedTestFamily F N)
    (q p : Fin N → F) :
    (f.weylCoefficients F N ψ hc hu hn hμ a ha h).value F (N + N)
      (fun i => algebraMap F (ArchimedeanAdeles.Construction.Adeles F) (WeylMidpoint.Construction.midpointRationalEquiv F N (q, p) i)) =
        ((f.correlation F N h q).act F N ψ a).value F N (fun i => algebraMap F (ArchimedeanAdeles.Construction.Adeles F) (p i)) := by
  apply tprod_congr
  intro v
  let := hμ v
  change WeylCoefficientTransport.Construction.positionWeylCoefficient (Characters.Construction.localAdditiveCharacter F ψ v)
      (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F v) N (Characters.Construction.localAdditiveCharacter F ψ v)) (f v).val (h v).val
      (fun i => ArchimedeanAdeles.Construction.rationalScalar F v (WeylMidpoint.Construction.midpointRationalEquiv F N (q, p) i)) =
    (Oscillator.Construction.localOperator (ArchimedeanAdeles.Construction.Completion F v) N (Characters.Construction.localAdditiveCharacter F ψ v) (a v)
      ((f.correlation F N h q) v)).val (fun i => ArchimedeanAdeles.Construction.rationalScalar F v (p i))
  rw [ha.2, WeylCoefficientTransport.Construction.positionWeylCoefficient, WeylTheta.Construction.midpointRationalEquiv_local]
  have hh := WeylMidpoint.Construction.weylMatrixCoefficient_midpoint_fourier (Characters.Construction.localAdditiveCharacter F ψ v)
    (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F v) N (Characters.Construction.localAdditiveCharacter F ψ v)) (f v).val (h v).val
    (fun i => ArchimedeanAdeles.Construction.rationalScalar F v (q i)) (-(fun i => ArchimedeanAdeles.Construction.rationalScalar F v (p i)))
  simpa only [neg_neg] using! hh

theorem RestrictedTestFamilies.Construction.RestrictedTestFamily.weylCoefficients_theta_correlations (f h : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) :
    (f.weylCoefficients F N ψ hc hu hn hμ a ha h).theta F (N + N) =
      ∑' q : Fin N → F, ((f.correlation F N h q).act F N ψ a).theta F N := by
  let C := f.weylCoefficients F N ψ hc hu hn hμ a ha h
  let ff (r : Fin (N + N) → F) := C.value F (N + N) (fun i => algebraMap F (ArchimedeanAdeles.Construction.Adeles F) (r i))
  have hs : Summable ff := C.theta_summable F (N + N)
  have hh := hs.comp_injective (WeylMidpoint.Construction.midpointRationalEquiv F N).injective
  change Summable (fun z => ff (WeylMidpoint.Construction.midpointRationalEquiv F N z)) at hh
  change (∑' r, ff r) = _
  rw [← (WeylMidpoint.Construction.midpointRationalEquiv F N).tsum_eq ff, hh.tsum_prod]
  apply tsum_congr
  intro q
  apply tsum_congr
  intro p
  exact f.weylCoefficients_value_midpoint F N ψ hc hu hn hμ a ha h q p

include hc hu hn hμ in
theorem RestrictedTestFamilies.Construction.RestrictedTestFamily.weylCoefficients_theta_positive
    (hp : ∀ q : F, ψ (algebraMap F (ArchimedeanAdeles.Construction.Adeles F) q) = 1) (f h : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) :
    ∃ c : ℝ, 0 < c ∧
      (f.weylCoefficients F N ψ hc hu hn hμ a ha h).theta F (N + N) =
        (c : ℂ) * (f.theta F N * conj (h.theta F N)) := by
  obtain ⟨M, hM, hperiod⟩ := f.correlation_uniform_period F N h
  obtain ⟨c, hcpos, hct⟩ := UniformPoisson.Construction.theta_fourier_uniform_period F N ψ hc hu hp
    (fun v => hn (.inl v)) (fun v => hμ (.inr v)) (fun v => hμ (.inl v)) a ha M hM
  refine ⟨c, hcpos, ?_⟩
  rw [RestrictedTestFamilies.Construction.RestrictedTestFamily.weylCoefficients_theta_correlations]
  simp_rw [hct _ (hperiod _), tsum_mul_left, RestrictedTestFamilies.Construction.RestrictedTestFamily.tsum_correlation_theta]

end

end OAI.RepresentationTheory.Weil.AdelicSplitting
