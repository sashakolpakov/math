import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanFresnel
import OAI.RepresentationTheory.Weil.AdelicSplitting.LocalKernel
import OAI.RepresentationTheory.Weil.Local.Analytic

/-! # Local Fresnel -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.LocalFresnel

noncomputable section

/-! The exact Fourier-quadratic Gaussian relation at every actual
completion, with no separate analytic normalization assumption. -/

open _root_.MeasureTheory

namespace Analysis
open OAI.RepresentationTheory.Weil.Local.Analytic.Construction

theorem localField_fresnel
    {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hnd : ¬ DiscreteTopology k) (N : ℕ) (ψ : AddChar k ℂ)
    (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1)
    (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) (x : Local.FunctionsMetaplectic.Construction.Position k N) :
    Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Local.FunctionsMetaplectic.Construction.positionMeasure k N ψ)
      (Local.FunctionsMetaplectic.Construction.quadraticOperator ψ 1 (Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Local.FunctionsMetaplectic.Construction.positionMeasure k N ψ) f.val)) x =
      Local.FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 ^ N * ψ (-Local.FunctionsMetaplectic.Construction.quadratic 1 x) *
        Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Local.FunctionsMetaplectic.Construction.positionMeasure k N ψ) (Local.FunctionsMetaplectic.Construction.quadraticOperator ψ (-1) f.val) x := by
  let : SecondCountableTopology k := TestSpace.LocalAnalysis.localField_secondCountable k hnd
  by_cases hArch : ∀ m : ℕ, ‖(m : k)‖ ≤ 1
  · let : IsUltrametricDist k := IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one hArch
    exact Local.NormalizedFresnel.Construction.nonarchimedean_fourier_quadratic_fourier hnd ψ hu hc hn f x
  · rcases Local.ArchimedeanClassification.Construction.localField_archimedean_classification k hArch with ⟨e, he, hi⟩ | ⟨e, he, hi⟩
    · exact ArchimedeanFresnel.LocalAnalysis.realField_fresnel hArch e he hi N ψ hc hu hn f x
    · exact ArchimedeanFresnel.LocalAnalysis.complexField_fresnel hArch e he hi N ψ hc hu hn f x

end Analysis

namespace Construction
open OAI.RepresentationTheory.Weil.Local.Analytic.Construction OAI.RepresentationTheory.Weil.AdelicSplitting.LocalFresnel.Analysis

variable (F : Type) [Field F] [NumberField F] (N : ℕ)
variable (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1)
variable (hn : ∀ v : ArchimedeanAdeles.Construction.Places F, ∃ t : ArchimedeanAdeles.Construction.Completion F v, Characters.Construction.localAdditiveCharacter F ψ v t ≠ 1)

include hc hu hn in
theorem completion_fresnel (v : ArchimedeanAdeles.Construction.Places F) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F v) N)
    (x : Local.FunctionsMetaplectic.Construction.Position (ArchimedeanAdeles.Construction.Completion F v) N) :
    Local.FunctionsMetaplectic.Construction.fourierIntegral (Characters.Construction.localAdditiveCharacter F ψ v) (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F v) N (Characters.Construction.localAdditiveCharacter F ψ v))
      (Local.FunctionsMetaplectic.Construction.quadraticOperator (Characters.Construction.localAdditiveCharacter F ψ v) 1
        (Local.FunctionsMetaplectic.Construction.fourierIntegral (Characters.Construction.localAdditiveCharacter F ψ v) (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F v) N (Characters.Construction.localAdditiveCharacter F ψ v)) f.val)) x =
      Local.FunctionsMetaplectic.Construction.gaussianIndex (ArchimedeanAdeles.Construction.Completion F v) (Characters.Construction.localAdditiveCharacter F ψ v) 1 ^ N *
        Characters.Construction.localAdditiveCharacter F ψ v (-Local.FunctionsMetaplectic.Construction.quadratic 1 x) *
          Local.FunctionsMetaplectic.Construction.fourierIntegral (Characters.Construction.localAdditiveCharacter F ψ v) (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F v) N (Characters.Construction.localAdditiveCharacter F ψ v))
            (Local.FunctionsMetaplectic.Construction.quadraticOperator (Characters.Construction.localAdditiveCharacter F ψ v) (-1) f.val) x :=
  Analysis.localField_fresnel (LocalKernel.Construction.completion_nondiscrete F v) N (Characters.Construction.localAdditiveCharacter F ψ v)
    (Characters.Construction.localAdditiveCharacter_continuous F ψ hc v) (Characters.Construction.localAdditiveCharacter_unitary F ψ hu v) (hn v) f x

include N hc hu hn in
theorem completion_gaussianIndex_one_norm (v : ArchimedeanAdeles.Construction.Places F) :
    ‖Local.FunctionsMetaplectic.Construction.gaussianIndex (ArchimedeanAdeles.Construction.Completion F v) (Characters.Construction.localAdditiveCharacter F ψ v) 1‖ = 1 := by
  apply Local.FunctionsMetaplectic.Construction.gaussianIndex_norm
  exact ((Local.Analytic.Construction.localField_analytic_normalization (LocalKernel.Construction.completion_nondiscrete F v)
    (Characters.Construction.localAdditiveCharacter F ψ v) (Characters.Construction.localAdditiveCharacter_continuous F ψ hc v)
      (Characters.Construction.localAdditiveCharacter_unitary F ψ hu v) (hn v) N).2.2.1 1 one_ne_zero).2.1

end Construction

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.LocalFresnel
