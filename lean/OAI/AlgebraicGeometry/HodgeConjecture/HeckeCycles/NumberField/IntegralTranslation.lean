import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NumberField.LocalIntegral
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NumberField.HeisenbergFamily
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.PureFunctionExt

/-! # Integral Translation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NumberField.IntegralTranslation.CM

noncomputable section

/-! Translation invariance of the actual descended global integral is
proved from local Haar translation invariance and restricted pure tests. -/

open scoped Classical _root_.NumberField
open Filter _root_.MeasureTheory
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz
open OAI.RepresentationTheory.Theta.Adelic.Evaluation OAI.RepresentationTheory.Theta.Adelic.TensorProjective.Restricted

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

local instance (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) : MeasurableSpace (v.adicCompletion F) := borel _
local instance (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

def localTranslation (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) (q : Fin N → v.adicCompletion F) :
    RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N →ₗ[ℂ] RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N where
  toFun f := ⟨fun x => f.val (x - q), RepresentationTheory.Weil.Local.OscillatorSchur.Construction.schwartzBruhat_translate_mem q f.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem local_integral (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) (q : Fin N → v.adicCompletion F)
    (f : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N) :
    LocalIntegral.CM.integral F N v (localTranslation F N v q f) =
      LocalIntegral.CM.integral F N v f := by
  change (LocalIntegral.CM.mass F N v : ℂ)⁻¹ *
    (∫ x, f.val (x - q) ∂ LocalIntegral.CM.measure F N v) = _
  rw [integral_sub_right_eq_self]
  rfl

theorem family_restricted (q : Fin N → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F)
    (f : ∀ v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F, RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N)
    (hf : ∀ᶠ v in cofinite, f v = RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) :
    ∀ᶠ v in cofinite, localTranslation F N v (fun i => q i v) (f v) = RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v := by
  have hq : ∀ᶠ v in cofinite, ∀ i, q i v ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.mpr (fun i => (q i).property)
  filter_upwards [hf, hq] with v hv hi
  rw [hv]
  apply Subtype.ext
  change (fun x => (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v).val (x - fun i => q i v)) = (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v).val
  rw [HeisenbergFamily.CM.Family.vacuum_indicator]
  funext x
  exact if_congr (IntegralHeisenberg.CM.shifted_mem (v.adicCompletionIntegers F).toSubring
    (fun i => q i v) x hi) rfl rfl

def translation (q : Fin N → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :
    RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F N →ₗ[ℂ] RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F N where
  toFun f := ⟨fun x => f.val (x - q),
    f.property.1.comp_continuous (continuous_id.sub continuous_const),
    f.property.2.comp_homeomorph (Homeomorph.subRight q)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem translation_pure (q : Fin N → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F)
    (f : ∀ v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F, RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N)
    (hf : ∀ᶠ v in cofinite, f v = RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) :
    translation F N q (RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz F N (RepresentationTheory.Theta.Adelic.TensorProjective.Restricted.pure (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) f hf)) =
      RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz F N (RepresentationTheory.Theta.Adelic.TensorProjective.Restricted.pure (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N)
        (fun v => localTranslation F N v (fun i => q i v) (f v)) (family_restricted F N q f hf)) := by
  apply Subtype.ext
  funext x
  change RepresentationTheory.Theta.Adelic.Evaluation.finiteSchwartzFunction F N (RepresentationTheory.Theta.Adelic.TensorProjective.Restricted.pure (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) f hf) (x - q) =
    RepresentationTheory.Theta.Adelic.Evaluation.finiteSchwartzFunction F N (RepresentationTheory.Theta.Adelic.TensorProjective.Restricted.pure (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) _ _) x
  rw [RepresentationTheory.Theta.Adelic.Evaluation.finiteSchwartzFunction_pure, RepresentationTheory.Theta.Adelic.Evaluation.finiteSchwartzFunction_pure]
  rfl

theorem invariant (q : Fin N → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (φ : RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F N) :
    LocalIntegral.CM.globalIntegral F N (translation F N q φ) =
      LocalIntegral.CM.globalIntegral F N φ := by
  have h := Finite.PureFunctionExt.CM.ext F N
    ((LocalIntegral.CM.globalIntegral F N).comp (translation F N q))
    (LocalIntegral.CM.globalIntegral F N) (by
      intro f hf
      change LocalIntegral.CM.globalIntegral F N
        (translation F N q (RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz F N (RepresentationTheory.Theta.Adelic.TensorProjective.Restricted.pure (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) f hf))) = _
      rw [translation_pure]
      unfold LocalIntegral.CM.globalIntegral
      rw [Finite.FunctionAction.CM.FunctionalDescent.function_pure, Finite.FunctionAction.CM.FunctionalDescent.function_pure]
      apply finprod_congr
      intro v
      exact local_integral F N v _ _)
  exact congrArg (fun L : RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F N →ₗ[ℂ] ℂ => L φ) h

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NumberField.IntegralTranslation.CM
