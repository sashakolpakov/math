import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NumberField.LocalIntegral
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NumberField.HeisenbergFamily

/-! # Local Pairing -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NumberField.LocalPairing.CM

noncomputable section

/-! The actual local oscillator actions preserve Haar pairings,
normalized so the integral vacuum has squared norm one. -/

open scoped Classical _root_.NumberField
open _root_.MeasureTheory
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

local instance (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) : MeasurableSpace (v.adicCompletion F) := borel _
local instance (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

def pairing (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) (f h : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N) : ℂ :=
  (LocalIntegral.CM.mass F N v : ℂ)⁻¹ *
    ∫ x, f.val x * star (h.val x) ∂ LocalIntegral.CM.measure F N v

theorem unitary (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) (ψ : AddChar (v.adicCompletion F) ℂ)
    (g : RepresentationTheory.Weil.AdelicSplitting.Oscillator.Construction.LocalCover (v.adicCompletion F) N ψ)
    (f h : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N) :
    pairing F N v (RepresentationTheory.Weil.AdelicSplitting.Oscillator.Construction.localOperator (v.adicCompletion F) N ψ g f)
      (RepresentationTheory.Weil.AdelicSplitting.Oscillator.Construction.localOperator (v.adicCompletion F) N ψ g h) = pairing F N v f h := by
  have he := RepresentationTheory.Weil.Local.UnitaryInner.Construction.energy_preserving_inner (v.adicCompletion F) N
    (RepresentationTheory.Weil.AdelicSplitting.Oscillator.Construction.localOperator (v.adicCompletion F) N ψ g).toLinearMap g.property.1 h f
  rw [RepresentationTheory.Weil.Local.UnitaryInner.Construction.testToL2_inner, RepresentationTheory.Weil.Local.UnitaryInner.Construction.testToL2_inner] at he
  exact congrArg (fun z : ℂ => (LocalIntegral.CM.mass F N v : ℂ)⁻¹ * z) he

theorem vacuum (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) :
    pairing F N v (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) = 1 := by
  have he : (fun x => (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v).val x * star ((RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v).val x)) =
      (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v).val := by
    rw [HeisenbergFamily.CM.Family.vacuum_indicator]
    funext x
    unfold IntegralHeisenberg.CM.indicator
    split_ifs <;> simp
  change (LocalIntegral.CM.mass F N v : ℂ)⁻¹ *
    (∫ x, (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v).val x * star ((RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v).val x)
      ∂ LocalIntegral.CM.measure F N v) = 1
  rw [he]
  exact LocalIntegral.CM.vacuum F N v

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NumberField.LocalPairing.CM
