import OAI.RepresentationTheory.Weil.AdelicSplitting.FinitePositionInsert
import OAI.RepresentationTheory.Weil.AdelicSplitting.FiniteTensorFourier
import OAI.RepresentationTheory.Weil.AdelicSplitting.TestFamilyAction

/-! # Finite Fourier Relations -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.FiniteFourierRelations.Construction

noncomputable section

/-! The actual restricted Fourier operator preserves linear relations
between the finite-adelic values of restricted test families. The proof
integrates over one common finite set of exceptional places. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain Filter _root_.MeasureTheory

local instance finiteRelationMeasurableSpace (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) : MeasurableSpace (v.adicCompletion F) :=
  borel (v.adicCompletion F)

local instance finiteRelationBorelSpace (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

variable (F : Type) [Field F] [NumberField F] (N : ℕ)
variable (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ) (hu : ∀ x, ‖ψ x‖ = 1)
variable (hμ : ∀ v : HeightOneSpectrum (𝓞 F),
  (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F (.inr v)) N (Characters.Construction.localAdditiveCharacter F ψ (.inr v))).IsAddHaarMeasure)

include hc hu hμ in
theorem finite_fourier_preserves_relation {J : Type} [Fintype J]
    (a : Rational.Construction.RestrictedCover F N ψ) (ha : Rational.Construction.IsRationalFourier F N ψ a)
    (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) (g : J → RestrictedTestFamilies.Construction.RestrictedTestFamily F N) (c : J → ℂ)
    (hrel : ∀ x : Fin N → ArchimedeanAdeles.Construction.FiniteAdeles F, f.finiteValue F N x = ∑ j, c j * (g j).finiteValue F N x)
    (ξ : Fin N → ArchimedeanAdeles.Construction.FiniteAdeles F) :
    (f.act F N ψ a).finiteValue F N ξ = ∑ j, c j * ((g j).act F N ψ a).finiteValue F N ξ := by
  have ht : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      f (.inr v) = Vacuum.Construction.finiteVacuum F N v ∧
      (f.act F N ψ a) (.inr v) = Vacuum.Construction.finiteVacuum F N v ∧
      (∀ j, g j (.inr v) = Vacuum.Construction.finiteVacuum F N v) ∧
      (∀ j, ((g j).act F N ψ a) (.inr v) = Vacuum.Construction.finiteVacuum F N v) ∧
      ∀ i, ξ i v ∈ v.adicCompletionIntegers F := by
    filter_upwards [f.unramified, (f.act F N ψ a).unramified,
      eventually_all.mpr (fun j => (g j).unramified),
      eventually_all.mpr (fun j => ((g j).act F N ψ a).unramified),
      eventually_all.mpr (fun i => (ξ i).property)] with v hf hfa hg hga hξ
    exact ⟨hf, hfa, hg, hga, hξ⟩
  let bad := eventually_cofinite.mp ht
  let s := bad.toFinset
  have hout (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ s) :
      f (.inr v) = Vacuum.Construction.finiteVacuum F N v ∧
      (f.act F N ψ a) (.inr v) = Vacuum.Construction.finiteVacuum F N v ∧
      (∀ j, g j (.inr v) = Vacuum.Construction.finiteVacuum F N v) ∧
      (∀ j, ((g j).act F N ψ a) (.inr v) = Vacuum.Construction.finiteVacuum F N v) ∧
      ∀ i, ξ i v ∈ v.adicCompletionIntegers F := by
    simpa only [s, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] using hv
  let μ (v : s) := Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F (.inr v.val)) N (Characters.Construction.localAdditiveCharacter F ψ (.inr v.val))
  let : ∀ v : s, (μ v).IsAddHaarMeasure := fun v => hμ v.val
  let K (v : s) (x : Local.FunctionsMetaplectic.Construction.Position (ArchimedeanAdeles.Construction.Completion F (.inr v.val)) N) :=
    Characters.Construction.localAdditiveCharacter F ψ (.inr v.val) (-Local.FunctionsMetaplectic.Construction.dot (fun i => ξ i v.val) x)
  have hvalue (b : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) (hb : ∀ v ∉ s, b (.inr v) = Vacuum.Construction.finiteVacuum F N v) :
      b.finiteValue F N ξ = ∏ v : s, (b (.inr v.val)).val (fun i => ξ i v.val) := by
    have hξ : ξ ∈ FinitePositionInsert.Construction.finiteIntegralTail F N s := fun i v hv => (hout v hv).2.2.2.2 i
    rw [b.finiteValue_formula F N s hb, Set.indicator_of_mem hξ, mul_one, ← Finset.prod_coe_sort]
  have hF (b : RestrictedTestFamilies.Construction.RestrictedTestFamily F N)
      (hb : ∀ v ∉ s, (b.act F N ψ a) (.inr v) = Vacuum.Construction.finiteVacuum F N v) :
      (b.act F N ψ a).finiteValue F N ξ = ∏ v : s,
        ∫ x, (b (.inr v.val)).val x * K v x ∂μ v := by
    rw [hvalue _ hb]
    apply Finset.prod_congr rfl
    intro v _
    exact ha.2 (.inr v.val) (b (.inr v.val)) (fun i => ξ i v.val)
  have hg (j : J) (v : s) : Integrable (fun x => (g j (.inr v.val)).val x * K v x) (μ v) :=
    FourierTools.LocalAnalysis.fourierKernel_integrable (Characters.Construction.localAdditiveCharacter F ψ (.inr v.val))
      (Characters.Construction.localAdditiveCharacter_unitary F ψ hu (.inr v.val))
      (Characters.Construction.localAdditiveCharacter_continuous F ψ hc (.inr v.val)) (μ v)
      (TestSpace.LocalAnalysis.schwartzBruhat_integrable (μ v) (g j (.inr v.val))) (fun i => ξ i v.val)
  have hp (x : ∀ v : s, Local.FunctionsMetaplectic.Construction.Position (ArchimedeanAdeles.Construction.Completion F (.inr v.val)) N) :
      (∏ v : s, (f (.inr v.val)).val (x v)) = ∑ j, c j * ∏ v : s, (g j (.inr v.val)).val (x v) := by
    rw [← f.finiteValue_insert F N s (fun v hv => (hout v hv).1) x, hrel]
    apply Finset.sum_congr rfl
    intro j _
    rw [(g j).finiteValue_insert F N s (fun v hv => (hout v hv).2.2.1 j) x]
  calc
    _ = ∏ v : s, ∫ x, (f (.inr v.val)).val x * K v x ∂μ v :=
      hF f (fun v hv => (hout v hv).2.1)
    _ = ∑ j, c j * ∏ v : s, ∫ x, (g j (.inr v.val)).val x * K v x ∂μ v :=
      FiniteTensorFourier.Construction.finite_tensor_integral_relation μ (fun v => (f (.inr v.val)).val)
        (fun j v => (g j (.inr v.val)).val) c K hg hp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hF (g j) (fun v hv => (hout v hv).2.2.2.1 j)]

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.FiniteFourierRelations.Construction
