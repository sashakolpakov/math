import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NumberField.LocalPairing
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.PureFunctionExt

/-! # Test Products -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NumberField.TestProducts.CM

noncomputable section

/-! Pointwise products with conjugation preserve actual local and
global Schwartz functions and agree exactly on restricted pure tests. -/

open scoped Classical _root_.NumberField
open Filter Function
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz
open OAI.RepresentationTheory.Theta.Adelic.Evaluation OAI.RepresentationTheory.Theta.Adelic.TensorProjective.Restricted

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

def localProduct (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) (f h : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N) :
    RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N :=
  ⟨fun x => f.val x * star (h.val x), RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.compact_locallyConstant_mem
    ((RepresentationTheory.Weil.Local.NonarchimedeanTestSpace.Construction.schwartzBruhat_totallyDisconnected_iff.mp f.property).1.mul
      ((RepresentationTheory.Weil.Local.NonarchimedeanTestSpace.Construction.schwartzBruhat_totallyDisconnected_iff.mp h.property).1.comp star))
    (RepresentationTheory.Weil.Local.NonarchimedeanTestSpace.Construction.schwartzBruhat_totallyDisconnected_iff.mp f.property).2.mul_right⟩

theorem local_vacuum (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) :
    localProduct F N v (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) = RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v := by
  apply Subtype.ext
  change (fun x => (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v).val x * star ((RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v).val x)) = _
  rw [HeisenbergFamily.CM.Family.vacuum_indicator]
  funext x
  unfold IntegralHeisenberg.CM.indicator
  split_ifs <;> simp

theorem family_restricted
    (f h : ∀ v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F, RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N)
    (hf : ∀ᶠ v in cofinite, f v = RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v)
    (hh : ∀ᶠ v in cofinite, h v = RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) :
    ∀ᶠ v in cofinite, localProduct F N v (f v) (h v) = RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v := by
  filter_upwards [hf, hh] with v hf hh
  rw [hf, hh, local_vacuum]

def product (f h : RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F N) : RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F N :=
  ⟨fun x => f.val x * star (h.val x), f.property.1.mul (h.property.1.comp star), f.property.2.mul_right⟩

theorem pure_product
    (f h : ∀ v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F, RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N)
    (hf : ∀ᶠ v in cofinite, f v = RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v)
    (hh : ∀ᶠ v in cofinite, h v = RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) :
    product F N (RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz F N (RepresentationTheory.Theta.Adelic.TensorProjective.Restricted.pure (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) f hf))
      (RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz F N (RepresentationTheory.Theta.Adelic.TensorProjective.Restricted.pure (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) h hh)) =
      RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz F N (RepresentationTheory.Theta.Adelic.TensorProjective.Restricted.pure (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N)
        (fun v => localProduct F N v (f v) (h v)) (family_restricted F N f h hf hh)) := by
  apply Subtype.ext
  funext x
  change RepresentationTheory.Theta.Adelic.Evaluation.finiteSchwartzFunction F N (RepresentationTheory.Theta.Adelic.TensorProjective.Restricted.pure (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) f hf) x *
    star (RepresentationTheory.Theta.Adelic.Evaluation.finiteSchwartzFunction F N (RepresentationTheory.Theta.Adelic.TensorProjective.Restricted.pure (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) h hh) x) =
    RepresentationTheory.Theta.Adelic.Evaluation.finiteSchwartzFunction F N (RepresentationTheory.Theta.Adelic.TensorProjective.Restricted.pure (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) _ _) x
  rw [RepresentationTheory.Theta.Adelic.Evaluation.finiteSchwartzFunction_pure, RepresentationTheory.Theta.Adelic.Evaluation.finiteSchwartzFunction_pure, RepresentationTheory.Theta.Adelic.Evaluation.finiteSchwartzFunction_pure]
  have hs (u : ∀ v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F, RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N)
      (hu : ∀ᶠ v in cofinite, u v = RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) :
      HasFiniteMulSupport (fun v => (u v).val (fun i => x i v)) :=
    RepresentationTheory.Theta.Adelic.TensorProjective.Evaluation.evaluation_finite_support (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N)
      (RepresentationTheory.Theta.Adelic.Evaluation.localEvaluation F N x) (RepresentationTheory.Theta.Adelic.Evaluation.vacuum_evaluation_eventually_one F N x) u hu
  change (∏ᶠ v, (f v).val (fun i => x i v)) * star (∏ᶠ v, (h v).val (fun i => x i v)) =
    ∏ᶠ v, (f v).val (fun i => x i v) * star ((h v).val (fun i => x i v))
  have hstar : star (∏ᶠ v, (h v).val (fun i => x i v)) =
      ∏ᶠ v, star ((h v).val (fun i => x i v)) :=
    map_finprod (starRingEnd ℂ) (hs h hh)
  have hsstar : HasFiniteMulSupport (fun v => star ((h v).val (fun i => x i v))) := by
    filter_upwards [show ∀ᶠ v in cofinite, (h v).val (fun i => x i v) = 1 from hs h hh] with v hv
    change star ((h v).val (fun i => x i v)) = 1
    rw [hv, star_one]
  rw [hstar, finprod_mul_distrib (hs f hf) hsstar]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NumberField.TestProducts.CM
