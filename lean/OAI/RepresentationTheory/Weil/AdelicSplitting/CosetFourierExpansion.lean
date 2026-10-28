import OAI.RepresentationTheory.Weil.AdelicSplitting.CosetExpansion
import OAI.RepresentationTheory.Weil.AdelicSplitting.FiniteFourierRelations

/-! # Coset Fourier Expansion -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting

noncomputable section

/-! Finite coset expansions pass through the actual restricted Fourier
operator and through the absolutely convergent theta functional. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain _root_.MeasureTheory

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

theorem RestrictedTestFamilies.Construction.RestrictedTestFamily.value_of_finite_relation {J : Type} [Fintype J]
    (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) (g : J → RestrictedTestFamilies.Construction.RestrictedTestFamily F N) (c : J → ℂ)
    (ha : ∀ j v, g j (.inl v) = f (.inl v))
    (hf : ∀ x, f.finiteValue F N x = ∑ j, c j * (g j).finiteValue F N x)
    (x : Fin N → ArchimedeanAdeles.Construction.Adeles F) :
    f.value F N x = ∑ j, c j * (g j).value F N x := by
  rw [f.value_factorization F N, hf, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [(g j).value_factorization F N]
  simp_rw [ha]
  ring

theorem RestrictedTestFamilies.Construction.RestrictedTestFamily.theta_of_finite_relation {J : Type} [Fintype J]
    (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) (g : J → RestrictedTestFamilies.Construction.RestrictedTestFamily F N) (c : J → ℂ)
    (ha : ∀ j v, g j (.inl v) = f (.inl v))
    (hf : ∀ x, f.finiteValue F N x = ∑ j, c j * (g j).finiteValue F N x) :
    f.theta F N = ∑ j, c j * (g j).theta F N := by
  change (∑' q : Fin N → F, f.value F N (fun i => algebraMap F (ArchimedeanAdeles.Construction.Adeles F) (q i))) = _
  simp_rw [f.value_of_finite_relation F N g c ha hf]
  rw [Summable.tsum_finsetSum]
  · simp only [tsum_mul_left]
    rfl
  · intro j _
    exact ((g j).theta_summable F N).mul_left _

theorem RestrictedTestFamilies.Construction.RestrictedTestFamily.finite_coset_expansion (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) :
    ∃ M : ℕ, ∃ hM : 0 < M,
      ∃ s : Finset (FiniteCosets.Construction.FinitePositionQuotient (ι := Fin N) (M : F) (by exact_mod_cast hM.ne')),
        ∀ x : Fin N → ArchimedeanAdeles.Construction.FiniteAdeles F,
          f.finiteValue F N x = ∑ c : s,
            f.finiteValue F N (FiniteCosets.Construction.finiteRationalPosition (FiniteCosets.Construction.finitePositionQuotientRep (M : F) (by exact_mod_cast hM.ne') c.val)) *
              (f.replaceFiniteByCoset F N (M : F) (by exact_mod_cast hM.ne')
                (FiniteCosets.Construction.finiteRationalPosition (FiniteCosets.Construction.finitePositionQuotientRep (M : F) (by exact_mod_cast hM.ne') c.val))).finiteValue F N x := by
  obtain ⟨M, hM, hp⟩ := FiniteLattices.Construction.finite_locallyConstant_lattice_period (f.finiteValue F N)
    (f.finiteValue_locallyConstant F N) (f.finiteValue_compactSupport F N)
  let hm : (M : F) ≠ 0 := by exact_mod_cast hM.ne'
  obtain ⟨s, hs⟩ := FiniteCosets.Construction.finite_function_coset_expansion (f.finiteValue F N)
    (f.finiteValue_compactSupport F N) (M : F) hm hp
  refine ⟨M, hM, s, fun x => ?_⟩
  simp_rw [RestrictedTestFamilies.Construction.RestrictedTestFamily.replaceFiniteByCoset_finiteValue]
  exact (hs x).trans (Finset.sum_coe_sort s _).symm

local instance CosetFourierExpansion.Construction.cosetExpansionMeasurableSpace (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) : MeasurableSpace (v.adicCompletion F) :=
  borel (v.adicCompletion F)

local instance CosetFourierExpansion.Construction.cosetExpansionBorelSpace (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

theorem RestrictedTestFamilies.Construction.RestrictedTestFamily.theta_fourier_of_finite_relation
    (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ) (hu : ∀ x, ‖ψ x‖ = 1)
    (hμ : ∀ v : HeightOneSpectrum (𝓞 F),
      (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F (.inr v)) N (Characters.Construction.localAdditiveCharacter F ψ (.inr v))).IsAddHaarMeasure)
    {J : Type} [Fintype J]
    (a : Rational.Construction.RestrictedCover F N ψ) (ha : Rational.Construction.IsRationalFourier F N ψ a)
    (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) (g : J → RestrictedTestFamilies.Construction.RestrictedTestFamily F N) (c : J → ℂ)
    (harch : ∀ j v, g j (.inl v) = f (.inl v))
    (hrel : ∀ x, f.finiteValue F N x = ∑ j, c j * (g j).finiteValue F N x) :
    (f.act F N ψ a).theta F N = ∑ j, c j * ((g j).act F N ψ a).theta F N := by
  apply RestrictedTestFamilies.Construction.RestrictedTestFamily.theta_of_finite_relation
  · intro j v
    dsimp only [RestrictedTestFamilies.Construction.RestrictedTestFamily.act]
    rw [harch j v]
  · exact FiniteFourierRelations.Construction.finite_fourier_preserves_relation F N ψ hc hu hμ a ha f g c hrel

end

end OAI.RepresentationTheory.Weil.AdelicSplitting
