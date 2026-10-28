import OAI.RepresentationTheory.Theta.Adelic.UnramifiedNormCharacter
import OAI.RepresentationTheory.Theta.Adelic.UnramifiedAnnihilator
import OAI.RepresentationTheory.Theta.Adelic.IntegralTopology
import OAI.RepresentationTheory.Weil.AdelicSplitting.LocalKernel
import OAI.RepresentationTheory.Theta.Adelic.UnramifiedGaussian
import OAI.RepresentationTheory.Weil.AdelicSplitting.CorrectedGeneratorKernels

/-! # Norm Character Unramified -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Adelic.NormCharacterUnramified

/-! A single cofinite set of finite places on which the actual norm
character is trivial on every local integral unit. -/

open Filter
open scoped _root_.NumberField Classical

open OAI.RepresentationTheory.Theta.Adelic.FiniteCharacterNontrivial OAI.RepresentationTheory.Theta.Adelic.UnramifiedAnnihilator
open OAI.RepresentationTheory.Theta.Adelic.QuadraticNormCharacter

theorem normCharacter_unramified
    (F : Type) [Field F] [NumberField F] (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ)
    (hc : Continuous ψ) (hu : ∀ x, ‖ψ x‖ = 1) (hn : ∃ x, ψ x ≠ 1)
    (hp : ∀ q : F, ψ (algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) q) = 1)
    (d : F) (hd : d ≠ 0) :
    ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) in cofinite,
      ∀ a : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v))ˣ,
        a.val ∈ Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v) → a.val⁻¹ ∈ Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v) →
          Weil.AdelicSplitting.Characters.Construction.normCharacter F d (.inr v) a = 1 := by
  have ht : Tendsto (Sum.inr : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F)
      cofinite cofinite := Sum.inr_injective.tendsto_cofinite
  have hAnn := ht.eventually (UnramifiedAnnihilator.local_annihilator_integer F ψ hc hu hn hp)
  have hhalf := ht.eventually (Weil.AdelicSplitting.Integral.Construction.rationalScalar_integral F (2 : F)⁻¹)
  have hdi := ht.eventually (Weil.AdelicSplitting.Integral.Construction.rationalScalar_integral F d⁻¹)
  have hdv := ht.eventually (Weil.AdelicSplitting.Integral.Construction.rationalScalar_integral F d)
  filter_upwards [hAnn, hhalf, hdi, hdv, Weil.AdelicSplitting.UnramifiedCharacter.Construction.localAdditiveCharacter_unramified_finite F ψ hu hc]
    with v hAnn hhalf hdi hdv hψ
  intro a ha hai
  let : CharZero (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) := Weil.AdelicSplitting.ArchimedeanAdeles.Construction.completionCharZero F (.inr v)
  let : MeasurableSpace (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) := Weil.AdelicSplitting.ArchimedeanAdeles.Construction.completionMeasurableSpace F (.inr v)
  let : BorelSpace (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) := ⟨rfl⟩
  let k := Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)
  let S := Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v)
  have hSc : IsCompact (S : Set k) := by
    have he : (S : Set k) = Metric.closedBall 0 1 := by
      ext x
      simp only [Metric.mem_closedBall, dist_zero_right, Valued.toNormedField.norm_le_one_iff]
      rfl
    rw [he]
    exact isCompact_closedBall _ _
  have hnd := Weil.AdelicSplitting.LocalKernel.Construction.completion_nondiscrete F (.inr v)
  change QuadraticNormCharacter.normSign (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v) d) a = 1
  exact UnramifiedNormCharacter.normSign_integral_unit_of_normedField hnd
      (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ (.inr v))
      (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter_continuous F ψ hc (.inr v))
      (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter_unitary F ψ hu (.inr v))
      (FiniteCharacterNontrivial.local_character_nontrivial F ψ hc hu hn hp (.inr v)) S
      (IntegralTopology.localIntegerRing_open F (.inr v)) hSc hψ hAnn
      (by simpa only [map_inv₀, map_ofNat] using hhalf) _
      ((map_ne_zero (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v))).mpr hd) hdv
      (by simpa only [map_inv₀] using hdi) a ha hai

end RepresentationTheory.Theta.Adelic.NormCharacterUnramified

namespace RepresentationTheory.Theta.Adelic.NormCharacterUnramified.WeilConstant

/-! The corrected quadratic Weil factor equals one at all but finitely
many finite places, independently of any unitary splitting family. -/

open Filter
open scoped _root_.NumberField Classical

open OAI.RepresentationTheory.Theta.Adelic.FiniteCharacterNontrivial OAI.RepresentationTheory.Theta.Adelic.UnramifiedAnnihilator

variable (F : Type) [Field F] [NumberField F]

local instance (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    MeasurableSpace (v.adicCompletion F) := borel (v.adicCompletion F)
local instance (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    BorelSpace (v.adicCompletion F) := ⟨rfl⟩

theorem schrodingerWeilConstant_unramified (d : F) (hd : d ≠ 0)
    (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ) (hu : ∀ x, ‖ψ x‖ = 1)
    (hn : ∃ x, ψ x ≠ 1) (hp : ∀ q : F, ψ (algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) q) = 1) :
    ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) in cofinite,
      Weil.AdelicSplitting.CorrectedGeneratorKernels.Construction.schrodingerQuadraticWeilConstant (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v))
        (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ (.inr v)) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v) d) = 1 := by
  have ht : Tendsto (Sum.inr : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F)
      cofinite cofinite := Sum.inr_injective.tendsto_cofinite
  filter_upwards [ht.eventually (UnramifiedAnnihilator.local_annihilator_integer F ψ hc hu hn hp),
    ht.eventually (Weil.AdelicSplitting.Integral.Construction.rationalScalar_integral F (2 : F)⁻¹),
    ht.eventually (Weil.AdelicSplitting.Integral.Construction.rationalScalar_integral F d⁻¹), ht.eventually (Weil.AdelicSplitting.Integral.Construction.rationalScalar_integral F d),
    Weil.AdelicSplitting.UnramifiedCharacter.Construction.localAdditiveCharacter_unramified_finite F ψ hu hc] with v hAnn hhalf hdi hdv hψ
  let : MeasurableSpace (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) := Weil.AdelicSplitting.ArchimedeanAdeles.Construction.completionMeasurableSpace F (.inr v)
  let : BorelSpace (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) := ⟨rfl⟩
  let : CharZero (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) := Weil.AdelicSplitting.ArchimedeanAdeles.Construction.completionCharZero F (.inr v)
  let S := Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v)
  have hSc : IsCompact (S : Set (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v))) := by
    have he : (S : Set (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v))) = Metric.closedBall 0 1 := by
      ext x
      simp only [Metric.mem_closedBall, dist_zero_right, Valued.toNormedField.norm_le_one_iff]
      rfl
    rw [he]
    exact isCompact_closedBall _ _
  have hγ (a : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v))ˣ) (ha : a.val ∈ S) (hi : a.val⁻¹ ∈ S) :
      Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ (.inr v)) a.val = 1 :=
    UnramifiedGaussian.gaussianIndex_integral_unit (Weil.AdelicSplitting.LocalKernel.Construction.completion_nondiscrete F (.inr v))
      (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ (.inr v))
      (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter_continuous F ψ hc (.inr v))
      (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter_unitary F ψ hu (.inr v))
      (FiniteCharacterNontrivial.local_character_nontrivial F ψ hc hu hn hp (.inr v)) S
      (IntegralTopology.localIntegerRing_open F (.inr v)) hSc hψ hAnn
      (by simpa only [map_inv₀, map_ofNat] using hhalf) a ha hi
  have hneg := hγ (-1 : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v))ˣ) (S.neg_mem S.one_mem) (by simp)
  have hdγ := hγ (Units.mk0 (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v) d)
    ((map_ne_zero (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v))).mpr hd)) hdv
      (by simpa only [Units.val_mk0, map_inv₀] using hdi)
  change Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex _ _ (-1) * Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex _ _ (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v) d) = 1
  exact (congrArg₂ (· * ·) hneg hdγ).trans (one_mul 1)

end RepresentationTheory.Theta.Adelic.NormCharacterUnramified.WeilConstant

end

end OAI
