import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PadicCharacter
import OAI.RepresentationTheory.Hecke.RadialDilation.LocalLiftChoice
import OAI.RepresentationTheory.Weil.Local.NonarchimedeanBareKernel
import OAI.RepresentationTheory.Weil.Local.NonarchimedeanNormalization
import OAI.RepresentationTheory.Weil.Local.NonarchimedeanCover
import OAI.RepresentationTheory.Weil.Local.FourierEquivalence

/-! # Schrodinger -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.Schrodinger.CM

noncomputable section

/-! Actual local Schrödinger objects for the constructed p-adic
character. All analytic normalization and bare-kernel facts are supplied
by the proved LocalWeil constructions. -/

open scoped Classical
open _root_.MeasureTheory
open OAI.RepresentationTheory.Hecke.RadialDilation.LocalLiftChoice.Realization
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PadicCharacter.CM
variable (q n : ℕ) [Fact q.Prime]

local instance : MeasurableSpace ℚ_[q] := borel ℚ_[q]
local instance : BorelSpace ℚ_[q] := ⟨rfl⟩

abbrev Test := RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n
abbrev LocalOscillator := RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Oscillator ℚ_[q] n (PadicCharacter.CM.character q)
abbrev LocalMetaplectic := RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Metaplectic ℚ_[q] n (PadicCharacter.CM.character q)

def measure : Measure (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Position ℚ_[q] n) := RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.positionMeasure ℚ_[q] n (PadicCharacter.CM.character q)

instance measure_haar : (measure q n).IsAddHaarMeasure := by
  let : (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure ℚ_[q] (PadicCharacter.CM.character q)).IsAddHaarMeasure :=
    RepresentationTheory.Weil.Local.FourierTools.Construction.selfDualMeasure_isAddHaarMeasure_of_scale_pos _ _
      (RepresentationTheory.Weil.Local.NonarchimedeanHaar.Construction.nonarchimedean_reference_scale (RepresentationTheory.Hecke.RadialDilation.LocalLiftChoice.Realization.padic_not_discrete q) (PadicCharacter.CM.character q)
        (PadicCharacter.CM.character_unitary q) (PadicCharacter.CM.character_continuous q) (PadicCharacter.CM.character_nontrivial q)).1
  unfold measure RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.positionMeasure
  infer_instance

theorem fourier_mem (f : Test q n) :
    RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.fourierIntegral (PadicCharacter.CM.character q) (measure q n) f.val ∈ RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n :=
  RepresentationTheory.Weil.Local.CompactCharacter.Construction.nonarchimedean_fourier_mem (RepresentationTheory.Hecke.RadialDilation.LocalLiftChoice.Realization.padic_not_discrete q) (PadicCharacter.CM.character q)
    (PadicCharacter.CM.character_unitary q) (PadicCharacter.CM.character_continuous q) (PadicCharacter.CM.character_nontrivial q) (measure q n) f

theorem fourier_inversion (f : Test q n) (x : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Position ℚ_[q] n) :
    RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.fourierIntegral (PadicCharacter.CM.character q) (measure q n)
      (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.fourierIntegral (PadicCharacter.CM.character q) (measure q n) f.val) x = f.val (-x) :=
  RepresentationTheory.Weil.Local.NonarchimedeanNormalization.Construction.nonarchimedean_fourier_inversion_selfDual (RepresentationTheory.Hecke.RadialDilation.LocalLiftChoice.Realization.padic_not_discrete q) n (PadicCharacter.CM.character q)
    (PadicCharacter.CM.character_unitary q) (PadicCharacter.CM.character_continuous q) (PadicCharacter.CM.character_nontrivial q) f x

def fourier : LocalOscillator q n :=
  RepresentationTheory.Weil.Local.FourierEquivalence.Construction.fourierOscillator (PadicCharacter.CM.character q) (PadicCharacter.CM.character_unitary q)
    (PadicCharacter.CM.character_continuous q) (measure q n) (fourier_mem q n) (fourier_inversion q n)

theorem fourier_apply (f : Test q n) (x : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Position ℚ_[q] n) :
    ((fourier q n).val.2 f).val x = RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.fourierIntegral (PadicCharacter.CM.character q) (measure q n) f.val x := rfl

def quadratic (B : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.SymmetricMatrix ℚ_[q] n) : LocalMetaplectic q n :=
  RepresentationTheory.Weil.Local.NonarchimedeanTestSpace.Construction.nonarchimedeanQuadraticMetaplectic (RepresentationTheory.Hecke.RadialDilation.LocalLiftChoice.Realization.padic_not_discrete q) (PadicCharacter.CM.character q)
    (PadicCharacter.CM.character_unitary q) (PadicCharacter.CM.character_continuous q) B

theorem quadratic_apply (B : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.SymmetricMatrix ℚ_[q] n) (f : Test q n) (x : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Position ℚ_[q] n) :
    (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[q] n (PadicCharacter.CM.character q) (quadratic q n B) f).val x =
      PadicCharacter.CM.character q (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.quadratic B.val x) * f.val x := rfl

theorem projection_surjective : Function.Surjective (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℚ_[q] n (PadicCharacter.CM.character q)) :=
  RepresentationTheory.Weil.Local.NonarchimedeanCover.Construction.nonarchimedean_metaplecticProjection_surjective (RepresentationTheory.Hecke.RadialDilation.LocalLiftChoice.Realization.padic_not_discrete q) n (PadicCharacter.CM.character q)
    (PadicCharacter.CM.character_unitary q) (PadicCharacter.CM.character_continuous q) (PadicCharacter.CM.character_nontrivial q)

theorem kernel_sign (a : LocalMetaplectic q n)
    (ha : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℚ_[q] n (PadicCharacter.CM.character q) a = 1) :
    ∃ ε : ℂ, ε ^ 2 = 1 ∧ ∀ f : Test q n,
      RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[q] n (PadicCharacter.CM.character q) a f = ε • f :=
  RepresentationTheory.Weil.Local.NonarchimedeanBareKernel.Construction.nonarchimedean_metaplectic_kernel_sign (RepresentationTheory.Hecke.RadialDilation.LocalLiftChoice.Realization.padic_not_discrete q) (PadicCharacter.CM.character q)
    (PadicCharacter.CM.character_unitary q) (PadicCharacter.CM.character_continuous q) (PadicCharacter.CM.character_nontrivial q) a ha

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.Schrodinger.CM
