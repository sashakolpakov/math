import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FunctionAction
import OAI.RepresentationTheory.Weil.Local.UnitaryInner

/-! # Local Integral -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NumberField.LocalIntegral.CM

noncomputable section

/-! Actual local Haar integration, normalized so the integral lattice
vacuum has integral one at every finite place. -/

open scoped Classical _root_.NumberField
open _root_.MeasureTheory OAI.RepresentationTheory.Weil.Local.UnitaryInner.Construction
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

local instance (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) : MeasurableSpace (v.adicCompletion F) := borel _
local instance (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

def measure (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) : Measure (Fin N → v.adicCompletion F) :=
  RepresentationTheory.Weil.Local.UnitaryInner.Construction.referencePositionMeasure (v.adicCompletion F) N

instance measureHaar (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) : (measure F N v).IsAddHaarMeasure := by
  unfold measure RepresentationTheory.Weil.Local.UnitaryInner.Construction.referencePositionMeasure
  infer_instance

def mass (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) : ℝ := (measure F N v).real (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finitePositionLattice F N v)

theorem mass_pos (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) : 0 < mass F N v := by
  apply ENNReal.toReal_pos
  · apply ((RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finitePositionLattice_clopen F N v).isOpen.measure_pos (measure F N v) ?_).ne'
    exact ⟨0, fun _ _ => (v.adicCompletionIntegers F).zero_mem⟩
  · exact (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finitePositionLattice_compact F N v).measure_ne_top

def rawIntegral (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N →ₗ[ℂ] ℂ where
  toFun f := ∫ x, f.val x ∂ measure F N v
  map_add' f h := integral_add (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat_integrable _ f) (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat_integrable _ h)
  map_smul' c f := integral_smul c f.val

theorem raw_vacuum (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) :
    rawIntegral F N v (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) = (mass F N v : ℂ) := by
  change (∫ x, (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finitePositionLattice F N v).indicator (fun _ => (1 : ℂ)) x ∂ measure F N v) = _
  rw [integral_indicator (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finitePositionLattice_clopen F N v).isClosed.measurableSet]
  simp only [setIntegral_const, Complex.real_smul, mul_one]
  rfl

def integral (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N →ₗ[ℂ] ℂ :=
  (mass F N v : ℂ)⁻¹ • rawIntegral F N v

theorem vacuum (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) : integral F N v (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) = 1 := by
  change (mass F N v : ℂ)⁻¹ * rawIntegral F N v (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) = 1
  rw [raw_vacuum, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (mass_pos F N v).ne')]

def globalIntegral : RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F N →ₗ[ℂ] ℂ :=
  Finite.FunctionAction.CM.FunctionalDescent.functionFunctional F N (integral F N)
    (Filter.Eventually.of_forall (vacuum F N))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NumberField.LocalIntegral.CM
