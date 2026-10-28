import OAI.RepresentationTheory.Theta.Adelic.NormCharacterUnramified
import OAI.RepresentationTheory.Theta.Adelic.HeckeUnramified
import OAI.RepresentationTheory.Theta.Adelic.UnramifiedVacuumFourier

/-! # Unramified Place -/

namespace OAI.RepresentationTheory.Theta.Adelic.UnramifiedPlace.Data

noncomputable section

/-! One cofinite set on which all character and Fourier conditions
needed for the actual unramified splitting hold simultaneously. -/

open Filter
open scoped _root_.NumberField Classical

variable (F : Type) [Field F] [NumberField F] (d : F) (n m : ℕ)
variable (C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d n m)

local instance (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    MeasurableSpace (v.adicCompletion F) := borel (v.adicCompletion F)
local instance (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    BorelSpace (v.adicCompletion F) := ⟨rfl⟩

structure UnramifiedPlaceData (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : Prop where
  parameter_integral : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v) d ∈ Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v)
  parameter_inverse_integral : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v) d)⁻¹ ∈ Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v)
  half_integral : (2 : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v))⁻¹ ∈ Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v)
  additive_trivial : ∀ t ∈ Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v), Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ (.inr v) t = 1
  weil_trivial : Weil.AdelicSplitting.CorrectedGeneratorKernels.Construction.schrodingerQuadraticWeilConstant (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v))
    (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ (.inr v)) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v) d) = 1
  norm_trivial : ∀ a : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v))ˣ,
    a.val ∈ Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v) → a.val⁻¹ ∈ Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v) →
    Weil.AdelicSplitting.Characters.Construction.normCharacter F d (.inr v) a = 1
  first_character_trivial : ∀ a : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d (.inr v))ˣ,
    a.val ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d (.inr v) → a.inv ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d (.inr v) →
      Weil.AdelicSplitting.Characters.Construction.localCharacter F d C.χW (.inr v) a = 1
  second_character_trivial : ∀ a : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d (.inr v))ˣ,
    a.val ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d (.inr v) → a.inv ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d (.inr v) →
      Weil.AdelicSplitting.Characters.Construction.localCharacter F d C.χV (.inr v) a = 1
  vacuum_fourier : Weil.Local.FunctionsMetaplectic.Construction.fourierIntegral (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ (.inr v))
    (Weil.Local.FunctionsMetaplectic.Construction.positionMeasure (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) (n * m) (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ (.inr v)))
    (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F (n * m) v).val = (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F (n * m) v).val
  doubled_vacuum_fourier : Weil.Local.FunctionsMetaplectic.Construction.fourierIntegral (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ (.inr v))
    (Weil.Local.FunctionsMetaplectic.Construction.positionMeasure (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) (n * m + n * m) (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ (.inr v)))
    (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F (n * m + n * m) v).val = (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F (n * m + n * m) v).val

theorem unramifiedPlaceData_eventually (hd : d ≠ 0) :
    ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) in cofinite, UnramifiedPlaceData F d n m C v := by
  have ht : Tendsto (Sum.inr : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F)
      cofinite cofinite := Sum.inr_injective.tendsto_cofinite
  filter_upwards [ht.eventually (Weil.AdelicSplitting.Integral.Construction.rationalScalar_integral F d),
    ht.eventually (Weil.AdelicSplitting.Integral.Construction.rationalScalar_integral F d⁻¹), ht.eventually (Weil.AdelicSplitting.Integral.Construction.rationalScalar_integral F (2 : F)⁻¹),
    Weil.AdelicSplitting.UnramifiedCharacter.Construction.localAdditiveCharacter_unramified_finite F C.ψ C.ψ_unitary C.ψ_continuous,
    NormCharacterUnramified.WeilConstant.schrodingerWeilConstant_unramified F d hd C.ψ C.ψ_continuous
      C.ψ_unitary C.ψ_nontrivial C.ψ_principal,
    NormCharacterUnramified.normCharacter_unramified F C.ψ C.ψ_continuous C.ψ_unitary
      C.ψ_nontrivial C.ψ_principal d hd,
    HeckeUnramified.localCharacter_unramified_finite F d C.χW,
    HeckeUnramified.localCharacter_unramified_finite F d C.χV,
    UnramifiedVacuumFourier.vacuum_fourier_fixed_eventually F (n * m) C.ψ C.ψ_continuous
      C.ψ_unitary C.ψ_nontrivial C.ψ_principal,
    UnramifiedVacuumFourier.vacuum_fourier_fixed_eventually F (n * m + n * m) C.ψ C.ψ_continuous
      C.ψ_unitary C.ψ_nontrivial C.ψ_principal] with v hv hi hh ha hw hn hc₁ hc₂ hf hff
  exact ⟨hv, by simpa only [map_inv₀] using hi, by simpa only [map_inv₀, map_ofNat] using hh,
    ha, hw, hn, hc₁, hc₂, hf, hff⟩

end

end OAI.RepresentationTheory.Theta.Adelic.UnramifiedPlace.Data
