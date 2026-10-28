import OAI.RepresentationTheory.Weil.AdelicSplitting.BruhatProducts
import OAI.RepresentationTheory.Weil.AdelicSplitting.ThetaTest

/-! # Correlation Families -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting

noncomputable section

/-! Restricted translated correlations and a common finite period lattice. -/

open scoped Classical _root_.NumberField ComplexConjugate
open Filter IsDedekindDomain

open OAI.RepresentationTheory.Weil.AdelicSplitting.BruhatProducts.LocalAnalysis

local instance CorrelationFamilies.Construction.correlationFiniteCharZero (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) : CharZero (v.adicCompletion F) := ArchimedeanAdeles.Construction.completionCharZero F (.inr v)

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

theorem CorrelationFamilies.Construction.finiteVacuum_translate (v : HeightOneSpectrum (𝓞 F))
    (q x : Local.FunctionsMetaplectic.Construction.Position (v.adicCompletion F) N) (hq : ∀ i, q i ∈ v.adicCompletionIntegers F) :
    (Vacuum.Construction.finiteVacuum F N v).val (x + q) = (Vacuum.Construction.finiteVacuum F N v).val x := by
  have he : (∀ i, (x + q) i ∈ v.adicCompletionIntegers F) ↔ ∀ i, x i ∈ v.adicCompletionIntegers F := by
    constructor
    · intro h i
      have hi := (v.adicCompletionIntegers F).toSubring.sub_mem (h i) (hq i)
      simpa only [Pi.add_apply, add_sub_cancel_right] using! hi
    · intro h i
      exact (v.adicCompletionIntegers F).toSubring.add_mem (h i) (hq i)
  by_cases hx : ∀ i, x i ∈ v.adicCompletionIntegers F
  · rw [RestrictedTestFamilies.Construction.finiteVacuum_eq_one_of_integral F N v _ (he.mpr hx), RestrictedTestFamilies.Construction.finiteVacuum_eq_one_of_integral F N v _ hx]
  · rw [FinitePositionInsert.Construction.finiteVacuum_eq_zero_of_not_integral F N v _ (fun h => hx (he.mp h)),
      FinitePositionInsert.Construction.finiteVacuum_eq_zero_of_not_integral F N v _ hx]

theorem CorrelationFamilies.Construction.finiteVacuum_correlation (v : HeightOneSpectrum (𝓞 F))
    (q : Local.FunctionsMetaplectic.Construction.Position (ArchimedeanAdeles.Construction.Completion F (.inr v)) N) (hq : ∀ i, q i ∈ v.adicCompletionIntegers F) :
    BruhatProducts.LocalAnalysis.bruhatCorrelation (Vacuum.Construction.finiteVacuum F N v) (Vacuum.Construction.finiteVacuum F N v) q = Vacuum.Construction.finiteVacuum F N v := by
  apply Subtype.ext
  funext x
  change (Vacuum.Construction.finiteVacuum F N v).val (x - q) * conj ((Vacuum.Construction.finiteVacuum F N v).val (x + q)) = _
  rw [sub_eq_add_neg, CorrelationFamilies.Construction.finiteVacuum_translate F N v (-q) x (fun i => (v.adicCompletionIntegers F).toSubring.neg_mem (hq i)),
    CorrelationFamilies.Construction.finiteVacuum_translate F N v q x hq]
  by_cases hx : ∀ i, x i ∈ v.adicCompletionIntegers F
  · simp only [RestrictedTestFamilies.Construction.finiteVacuum_eq_one_of_integral F N v x hx, map_one, mul_one]
  · simp only [FinitePositionInsert.Construction.finiteVacuum_eq_zero_of_not_integral F N v x hx, map_zero, mul_zero]

def RestrictedTestFamilies.Construction.RestrictedTestFamily.correlation (f h : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) (q : Fin N → F) :
    RestrictedTestFamilies.Construction.RestrictedTestFamily F N where
  component v := BruhatProducts.LocalAnalysis.bruhatCorrelation (f v) (h v) (fun i => ArchimedeanAdeles.Construction.rationalScalar F v (q i))
  unramified := by
    have hint : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
        ∀ i, ArchimedeanAdeles.Construction.rationalScalar F (.inr v) (q i) ∈ v.adicCompletionIntegers F :=
      eventually_all.mpr (fun i => Sum.inr_injective.tendsto_cofinite.eventually (Integral.Construction.rationalScalar_integral F (q i)))
    filter_upwards [f.unramified, h.unramified, hint] with v hf hh hq
    rw [hf, hh]
    exact CorrelationFamilies.Construction.finiteVacuum_correlation F N v _ hq

theorem RestrictedTestFamilies.Construction.RestrictedTestFamily.correlation_value (f h : RestrictedTestFamilies.Construction.RestrictedTestFamily F N)
    (q : Fin N → F) (x : Fin N → ArchimedeanAdeles.Construction.Adeles F) :
    (f.correlation F N h q).value F N x =
      f.value F N (x - fun i => algebraMap F (ArchimedeanAdeles.Construction.Adeles F) (q i)) *
        conj (h.value F N (x + fun i => algebraMap F (ArchimedeanAdeles.Construction.Adeles F) (q i))) := by
  apply ((f.correlation F N h q).localValue_hasProd F N x).unique
  convert (f.localValue_hasProd F N (x - fun i => algebraMap F (ArchimedeanAdeles.Construction.Adeles F) (q i))).mul
    ((h.localValue_hasProd F N (x + fun i => algebraMap F (ArchimedeanAdeles.Construction.Adeles F) (q i))).map
      (starRingEnd ℂ).toMonoidHom Complex.continuous_conj) using 1
  · funext v
    simp only [RestrictedTestFamilies.Construction.RestrictedTestFamily.localValue, RestrictedTestFamilies.Construction.RestrictedTestFamily.correlation,
      BruhatProducts.LocalAnalysis.bruhatCorrelation, Function.comp_apply, Pi.sub_apply, Pi.add_apply, map_sub, map_add]
    rfl

theorem RestrictedTestFamilies.Construction.RestrictedTestFamily.finiteValue_hasProd (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N)
    (x : Fin N → ArchimedeanAdeles.Construction.FiniteAdeles F) :
    HasProd (fun v : HeightOneSpectrum (𝓞 F) => (f (.inr v)).val (fun i => x i v)) (f.finiteValue F N x) :=
  (multipliable_of_hasFiniteMulSupport
    (eventually_cofinite.mp (f.finite_localValue_eventually_one F N x))).hasProd

theorem RestrictedTestFamilies.Construction.RestrictedTestFamily.correlation_finiteValue (f h : RestrictedTestFamilies.Construction.RestrictedTestFamily F N)
    (q : Fin N → F) (x : Fin N → ArchimedeanAdeles.Construction.FiniteAdeles F) :
    (f.correlation F N h q).finiteValue F N x =
      f.finiteValue F N (x - FiniteCosets.Construction.finiteRationalPosition q) *
        conj (h.finiteValue F N (x + FiniteCosets.Construction.finiteRationalPosition q)) := by
  exact ((f.correlation F N h q).finiteValue_hasProd F N x).unique
    ((f.finiteValue_hasProd F N (x - FiniteCosets.Construction.finiteRationalPosition q)).mul
      ((h.finiteValue_hasProd F N (x + FiniteCosets.Construction.finiteRationalPosition q)).map
        (starRingEnd ℂ).toMonoidHom Complex.continuous_conj))

theorem RestrictedTestFamilies.Construction.RestrictedTestFamily.common_finite_period (f h : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) :
    ∃ M : ℕ, ∃ hM : 0 < M,
      ∀ u ∈ FiniteLattices.Construction.finiteAdelicPositionLattice (ι := Fin N) (M : F) (by exact_mod_cast hM.ne'), ∀ x,
        f.finiteValue F N (u + x) = f.finiteValue F N x ∧
          h.finiteValue F N (u + x) = h.finiteValue F N x := by
  let U : OpenAddSubgroup (Fin N → ArchimedeanAdeles.Construction.FiniteAdeles F) :=
    ⟨FiniteLattices.Construction.functionTranslationStabilizer (f.finiteValue F N),
      FiniteLattices.Construction.functionTranslationStabilizer_isOpen _ (f.finiteValue_locallyConstant F N) (f.finiteValue_compactSupport F N)⟩
  let V : OpenAddSubgroup (Fin N → ArchimedeanAdeles.Construction.FiniteAdeles F) :=
    ⟨FiniteLattices.Construction.functionTranslationStabilizer (h.finiteValue F N),
      FiniteLattices.Construction.functionTranslationStabilizer_isOpen _ (h.finiteValue_locallyConstant F N) (h.finiteValue_compactSupport F N)⟩
  obtain ⟨M, hM, hp⟩ := FiniteLattices.Construction.finitePosition_open_integer_multiple F (U ⊓ V)
  refine ⟨M, hM, ?_⟩
  rintro u ⟨v, hv, rfl⟩ x
  let w : Fin N → IntegralAdeles.Construction.finiteIntegralRing F := fun i => ⟨v i, hv i⟩
  have hh := hp w
  change (∀ x, f.finiteValue F N (M • v + x) = f.finiteValue F N x) ∧
    (∀ x, h.finiteValue F N (M • v + x) = h.finiteValue F N x) at hh
  change f.finiteValue F N (FiniteLattices.Construction.finitePositionScale (M : F) v + x) = _ ∧
    h.finiteValue F N (FiniteLattices.Construction.finitePositionScale (M : F) v + x) = _
  rw [FiniteLattices.Construction.finitePositionScale_natCast]
  exact ⟨hh.1 x, hh.2 x⟩

theorem RestrictedTestFamilies.Construction.RestrictedTestFamily.correlation_uniform_period (f h : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) :
    ∃ M : ℕ, ∃ hM : 0 < M, ∀ q : Fin N → F,
      ∀ u ∈ FiniteLattices.Construction.finiteAdelicPositionLattice (ι := Fin N) (M : F) (by exact_mod_cast hM.ne'), ∀ x,
        (f.correlation F N h q).finiteValue F N (u + x) = (f.correlation F N h q).finiteValue F N x := by
  obtain ⟨M, hM, hp⟩ := f.common_finite_period F N h
  refine ⟨M, hM, fun q u hu x => ?_⟩
  simp only [RestrictedTestFamilies.Construction.RestrictedTestFamily.correlation_finiteValue, add_sub_assoc, add_assoc,
    (hp u hu _).1, (hp u hu _).2]

end

end OAI.RepresentationTheory.Weil.AdelicSplitting
