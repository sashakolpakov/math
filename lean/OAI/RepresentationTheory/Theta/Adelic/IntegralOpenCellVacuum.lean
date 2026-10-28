import OAI.RepresentationTheory.Theta.Adelic.IntegralTensor
import OAI.RepresentationTheory.Theta.Adelic.IntegralWeakVacuum
import OAI.RepresentationTheory.Theta.Adelic.IntegralNormalizationScalars
import OAI.RepresentationTheory.Theta.Adelic.UnramifiedPlace

/-! # Integral Open Cell Vacuum -/

namespace OAI.RepresentationTheory.Theta.Adelic.IntegralOpenCellVacuum

noncomputable section

/-! The actual normalized unitary splitting fixes the standard vacuum
on both integral unimodular open cells. -/

open _root_.MeasureTheory
open scoped Classical _root_.NumberField ComplexConjugate

open OAI.RepresentationTheory.Theta.Adelic.GlobalFrameIntegral OAI.RepresentationTheory.Theta.Adelic.IntegralTensor.OpenCell OAI.RepresentationTheory.Theta.Adelic.UnramifiedPlace.Data
open OAI.RepresentationTheory.Theta.Adelic.IntegralNormalizationScalars OAI.RepresentationTheory.Theta.Adelic.IntegralWeakVacuum

variable (F : Type) [Field F] [NumberField F] (d : F) (hd : d ≠ 0) (n m : ℕ)
variable (H : (Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
variable (K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
variable (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d n m H K) (C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d n m)
variable (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
local instance : MeasurableSpace (v.adicCompletion F) := borel (v.adicCompletion F)
local instance : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
variable (hv : UnramifiedPlace.Data.UnramifiedPlaceData F d n m C v)
variable (hP : GlobalFrameIntegral.IntegralFrameAt F d n m H K P (.inr v))
variable (hHI : ∀ i j, (Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d H (.inr v)).val i j ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d (.inr v))
variable (hHi : ∀ i j, (Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d H (.inr v)).inv i j ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d (.inr v))
variable (hKI : ∀ i j, (Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d K (.inr v)).val i j ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d (.inr v))
variable (hKi : ∀ i j, (Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d K (.inr v)).inv i j ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d (.inr v))
variable (s : (Weil.AdelicSplitting.Integral.Construction.LocalUnitary F H.val (.inr v) × Weil.AdelicSplitting.Integral.Construction.LocalUnitary F K.val (.inr v)) →ₜ* Weil.AdelicSplitting.Vacuum.Construction.CoverAt F (n * m) C.ψ (.inr v))
variable (hs : Weil.AdelicSplitting.CorrectedNormalization.Construction.CorrectedLocalNormalization F d hd n m C (.inr v)
  (Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d H (.inr v)) (Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d K (.inr v)) (P.localFrame (.inr v)) s)

include hv hP hHI hHi hKI hKi hs

theorem first_openCell_fixes_vacuum
    (hK : (Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d K (.inr v)).val.conjTranspose = -(Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d K (.inr v)).val)
    (g : Weil.AdelicSplitting.Integral.Construction.LocalUnitary F H.val (.inr v))
    (u : (Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d (.inr v)))ˣ) (hu : u.val = g.val.val - 1)
    (hui : ∀ i j, u.val i j ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d (.inr v))
    (hui' : ∀ i j, u.inv i j ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d (.inr v)) :
    Weil.AdelicSplitting.Oscillator.Construction.localOperator (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) (n * m) (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ (.inr v))
      (s (g, 1)) (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F (n * m) v) = Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F (n * m) v := by
  let : (Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ (.inr v))).IsAddHaarMeasure :=
    LocalFourier.local_selfDualMeasure_isAddHaarMeasure F C.ψ C.ψ_continuous C.ψ_unitary
      C.ψ_nontrivial C.ψ_principal (.inr v)
  have hD := IntegralTensor.OpenCell.firstDifference_val F d n m H K P (.inr v) g u hu
  have hi := IntegralTensor.OpenCell.firstDifference_integral F d n m H K P (.inr v) hP u hui hui'
  apply IntegralWeakVacuum.oscillator_fixes_integral_vacuum F (n * m) v _ hv.vacuum_fourier hv.doubled_vacuum_fourier
    hv.additive_trivial hv.half_integral _ (IntegralTensor.OpenCell.firstDifference F d n m H K P (.inr v) u) hD hi.1 hi.2 (s (g, 1))
  have hnorm := hs.1 g u hu (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F (n * m) v) (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F (n * m) v)
  have hc := IntegralNormalizationScalars.correctedFirstFactorScalar_integral F d hd (.inr v) hv.parameter_inverse_integral
    hv.parameter_integral hv.norm_trivial C hv.weil_trivial hv.first_character_trivial
    (Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d H (.inr v)) (Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d K (.inr v)) hK hHI hHi hKI hKi u hui hui'
  rw [hc, one_mul] at hnorm
  exact hnorm

theorem second_openCell_fixes_vacuum
    (hH : (Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d H (.inr v)).val.conjTranspose = (Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d H (.inr v)).val)
    (g : Weil.AdelicSplitting.Integral.Construction.LocalUnitary F K.val (.inr v))
    (u : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d (.inr v)))ˣ) (hu : u.val = g.val.val - 1)
    (hui : ∀ i j, u.val i j ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d (.inr v))
    (hui' : ∀ i j, u.inv i j ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d (.inr v)) :
    Weil.AdelicSplitting.Oscillator.Construction.localOperator (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) (n * m) (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ (.inr v))
      (s (1, g)) (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F (n * m) v) = Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F (n * m) v := by
  let : (Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ (.inr v))).IsAddHaarMeasure :=
    LocalFourier.local_selfDualMeasure_isAddHaarMeasure F C.ψ C.ψ_continuous C.ψ_unitary
      C.ψ_nontrivial C.ψ_principal (.inr v)
  have hD := IntegralTensor.OpenCell.secondDifference_val F d n m H K P (.inr v) g u hu
  have hi := IntegralTensor.OpenCell.secondDifference_integral F d n m H K P (.inr v) hP u hui hui'
  apply IntegralWeakVacuum.oscillator_fixes_integral_vacuum F (n * m) v _ hv.vacuum_fourier hv.doubled_vacuum_fourier
    hv.additive_trivial hv.half_integral _ (IntegralTensor.OpenCell.secondDifference F d n m H K P (.inr v) u) hD hi.1 hi.2 (s (1, g))
  have hnorm := hs.2 g u hu (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F (n * m) v) (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F (n * m) v)
  have hc := IntegralNormalizationScalars.correctedSecondFactorScalar_integral F d (.inr v) hv.parameter_integral hv.norm_trivial
    C hv.weil_trivial hv.second_character_trivial (Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d H (.inr v))
    (Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d K (.inr v)) hH hHI hHi hKI hKi u hui hui'
  rw [hc, one_mul] at hnorm
  exact hnorm

end

end OAI.RepresentationTheory.Theta.Adelic.IntegralOpenCellVacuum
