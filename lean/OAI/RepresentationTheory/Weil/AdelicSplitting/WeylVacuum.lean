import OAI.RepresentationTheory.Weil.AdelicSplitting.CorrelationFamilies
import OAI.RepresentationTheory.Weil.AdelicSplitting.WeylCoefficientTransport
import OAI.RepresentationTheory.Weil.UnitarySplitting.UltraWeylCoefficients

/-! # Weyl Vacuum -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.WeylVacuum.Construction

noncomputable section

/-! The Weyl coefficient of the unramified vacuum is the doubled vacuum. -/

open _root_.MeasureTheory IsDedekindDomain
open scoped Classical _root_.NumberField ComplexConjugate

local instance weylVacuumFiniteMeasurable (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) : MeasurableSpace (v.adicCompletion F) := borel (v.adicCompletion F)
local instance weylVacuumFiniteBorel (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

variable (F : Type) [Field F] [NumberField F] (N : ℕ) (v : HeightOneSpectrum (𝓞 F))

theorem finiteVacuum_mul_conj (x : Local.FunctionsMetaplectic.Construction.Position (v.adicCompletion F) N) :
    (Vacuum.Construction.finiteVacuum F N v).val x * conj ((Vacuum.Construction.finiteVacuum F N v).val x) = (Vacuum.Construction.finiteVacuum F N v).val x := by
  by_cases hx : ∀ i, x i ∈ v.adicCompletionIntegers F
  · simp only [RestrictedTestFamilies.Construction.finiteVacuum_eq_one_of_integral F N v x hx, map_one, mul_one]
  · simp only [FinitePositionInsert.Construction.finiteVacuum_eq_zero_of_not_integral F N v x hx, map_zero, mul_zero]

theorem finiteVacuum_neg (x : Local.FunctionsMetaplectic.Construction.Position (v.adicCompletion F) N) :
    (Vacuum.Construction.finiteVacuum F N v).val (-x) = (Vacuum.Construction.finiteVacuum F N v).val x := by
  have hh : (∀ i, (-x) i ∈ v.adicCompletionIntegers F) ↔ ∀ i, x i ∈ v.adicCompletionIntegers F := by
    change (∀ i, -x i ∈ (v.adicCompletionIntegers F).toSubring) ↔
      ∀ i, x i ∈ (v.adicCompletionIntegers F).toSubring
    simp only [neg_mem_iff]
  by_cases hx : ∀ i, x i ∈ v.adicCompletionIntegers F
  · rw [RestrictedTestFamilies.Construction.finiteVacuum_eq_one_of_integral F N v _ (hh.mpr hx), RestrictedTestFamilies.Construction.finiteVacuum_eq_one_of_integral F N v _ hx]
  · rw [FinitePositionInsert.Construction.finiteVacuum_eq_zero_of_not_integral F N v _ (fun h => hx (hh.mp h)),
      FinitePositionInsert.Construction.finiteVacuum_eq_zero_of_not_integral F N v _ hx]

theorem finiteVacuum_weyl_coefficient (ψ : AddChar (ArchimedeanAdeles.Construction.Completion F (.inr v)) ℂ)
    (μ : Measure (Local.FunctionsMetaplectic.Construction.Position (ArchimedeanAdeles.Construction.Completion F (.inr v)) N))
    (hF : Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ (Vacuum.Construction.finiteVacuum F N v).val = (Vacuum.Construction.finiteVacuum F N v).val)
    (hψ : ∀ t ∈ Integral.Construction.localIntegerRing F (.inr v), ψ t = 1)
    (hhalf : (2 : ArchimedeanAdeles.Construction.Completion F (.inr v))⁻¹ ∈ Integral.Construction.localIntegerRing F (.inr v))
    (w : Local.FunctionsMetaplectic.Construction.PhaseSpace (ArchimedeanAdeles.Construction.Completion F (.inr v)) N) :
    UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ μ (Vacuum.Construction.finiteVacuum F N v).val (Vacuum.Construction.finiteVacuum F N v).val w =
      (Vacuum.Construction.finiteVacuum F N v).val (UnitarySplitting.FourierCovariance.Construction.phasePosition w) * (Vacuum.Construction.finiteVacuum F N v).val (UnitarySplitting.FourierCovariance.Construction.phaseMomentum w) := by
  by_cases hq : ∀ i, UnitarySplitting.FourierCovariance.Construction.phasePosition w i ∈ v.adicCompletionIntegers F
  · rw [UnitarySplitting.UltraWeylCoefficients.Construction.weylMatrixCoefficient_fourier]
    have hf : (fun x => (Vacuum.Construction.finiteVacuum F N v).val (x - UnitarySplitting.FourierCovariance.Construction.phasePosition w) * conj ((Vacuum.Construction.finiteVacuum F N v).val x)) =
        (Vacuum.Construction.finiteVacuum F N v).val := by
      funext x
      rw [sub_eq_add_neg, CorrelationFamilies.Construction.finiteVacuum_translate F N v (-UnitarySplitting.FourierCovariance.Construction.phasePosition w) x
        (fun i => (v.adicCompletionIntegers F).toSubring.neg_mem (hq i)), finiteVacuum_mul_conj]
    rw [hf, hF, finiteVacuum_neg, RestrictedTestFamilies.Construction.finiteVacuum_eq_one_of_integral F N v _ hq, one_mul]
    by_cases hp : ∀ i, UnitarySplitting.FourierCovariance.Construction.phaseMomentum w i ∈ v.adicCompletionIntegers F
    · rw [RestrictedTestFamilies.Construction.finiteVacuum_eq_one_of_integral F N v _ hp, mul_one]
      apply hψ
      apply (Integral.Construction.localIntegerRing F (.inr v)).neg_mem
      apply (Integral.Construction.localIntegerRing F (.inr v)).sum_mem
      intro i _
      exact (Integral.Construction.localIntegerRing F (.inr v)).mul_mem (hp i)
        ((Integral.Construction.localIntegerRing F (.inr v)).mul_mem hhalf (hq i))
    · rw [FinitePositionInsert.Construction.finiteVacuum_eq_zero_of_not_integral F N v _ hp, mul_zero]
  · rw [FinitePositionInsert.Construction.finiteVacuum_eq_zero_of_not_integral F N v _ hq, zero_mul]
    apply integral_eq_zero_of_ae
    exact Filter.Eventually.of_forall fun x => by
      by_cases hx : ∀ i, x i ∈ v.adicCompletionIntegers F
      · have hs : ¬ ∀ i, (x - UnitarySplitting.FourierCovariance.Construction.phasePosition w) i ∈ v.adicCompletionIntegers F := by
          intro hs
          apply hq
          intro i
          have hi := (v.adicCompletionIntegers F).toSubring.sub_mem (hx i) (hs i)
          simpa only [Pi.sub_apply, sub_sub_cancel] using! hi
        simp only [UnitarySplitting.FourierCovariance.Construction.heisenbergFunction_dot,
          FinitePositionInsert.Construction.finiteVacuum_eq_zero_of_not_integral F N v _ hs, mul_zero, zero_mul, Pi.zero_apply]
      · simp only [FinitePositionInsert.Construction.finiteVacuum_eq_zero_of_not_integral F N v _ hx, map_zero, mul_zero, Pi.zero_apply]

theorem finiteVacuum_phaseCoordinates (w : Local.FunctionsMetaplectic.Construction.PhaseSpace (ArchimedeanAdeles.Construction.Completion F (.inr v)) N) :
    (Vacuum.Construction.finiteVacuum F (N + N) v).val (PhaseMeasure.Construction.phaseCoordinates (ArchimedeanAdeles.Construction.Completion F (.inr v)) N w) =
      (Vacuum.Construction.finiteVacuum F N v).val (UnitarySplitting.FourierCovariance.Construction.phasePosition w) * (Vacuum.Construction.finiteVacuum F N v).val (UnitarySplitting.FourierCovariance.Construction.phaseMomentum w) := by
  have heval (j : Fin N ⊕ Fin N) :
      PhaseMeasure.Construction.phaseCoordinates (ArchimedeanAdeles.Construction.Completion F (.inr v)) N w (finSumFinEquiv j) = w j := by
    exact Homeomorph.piCongrLeft_apply_apply
      (Y := fun _ : Fin (N + N) => ArchimedeanAdeles.Construction.Completion F (.inr v)) finSumFinEquiv w j
  have he : (∀ i, PhaseMeasure.Construction.phaseCoordinates (ArchimedeanAdeles.Construction.Completion F (.inr v)) N w i ∈ v.adicCompletionIntegers F) ↔
      (∀ i, UnitarySplitting.FourierCovariance.Construction.phasePosition w i ∈ v.adicCompletionIntegers F) ∧
        (∀ i, UnitarySplitting.FourierCovariance.Construction.phaseMomentum w i ∈ v.adicCompletionIntegers F) := by
    constructor
    · intro h
      constructor
      · intro i
        simpa only [heval] using! h (finSumFinEquiv (.inl i))
      · intro i
        simpa only [heval] using! h (finSumFinEquiv (.inr i))
    · rintro ⟨hq, hp⟩ i
      obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
      cases j with
      | inl j => simpa only [heval] using! hq j
      | inr j => simpa only [heval] using! hp j
  by_cases hq : ∀ i, UnitarySplitting.FourierCovariance.Construction.phasePosition w i ∈ v.adicCompletionIntegers F
  · rw [RestrictedTestFamilies.Construction.finiteVacuum_eq_one_of_integral F N v _ hq, one_mul]
    by_cases hp : ∀ i, UnitarySplitting.FourierCovariance.Construction.phaseMomentum w i ∈ v.adicCompletionIntegers F
    · rw [RestrictedTestFamilies.Construction.finiteVacuum_eq_one_of_integral F (N + N) v _ (he.mpr ⟨hq, hp⟩),
        RestrictedTestFamilies.Construction.finiteVacuum_eq_one_of_integral F N v _ hp]
    · rw [FinitePositionInsert.Construction.finiteVacuum_eq_zero_of_not_integral F (N + N) v _ (fun h => hp (he.mp h).2),
        FinitePositionInsert.Construction.finiteVacuum_eq_zero_of_not_integral F N v _ hp]
  · rw [FinitePositionInsert.Construction.finiteVacuum_eq_zero_of_not_integral F (N + N) v _ (fun h => hq (he.mp h).1),
      FinitePositionInsert.Construction.finiteVacuum_eq_zero_of_not_integral F N v _ hq, zero_mul]

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.WeylVacuum.Construction
