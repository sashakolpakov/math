import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.EvaluationKernel
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.TensorRepresentatives
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SurjectiveRepresentationDescent

/-! # Function Action -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FunctionAction.CM

/-! Construct the genuine action of the finite restricted group on actual
locally constant compactly supported adelic functions, with exact
intertwining from the original restricted tensor action. -/

open scoped Classical _root_.NumberField
open Filter
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.Evaluation
open OAI.RepresentationTheory.Theta.Adelic.TensorProjective.Restricted OAI.RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

instance tensorAddCommGroup : AddCommGroup (RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F N) :=
  Module.addCommMonoidToAddCommGroup ℂ

theorem section_identity (φ : RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F N) :
    RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz F N (TensorRepresentatives.CM.sectionMap F N φ) = φ := by
  apply Subtype.ext
  funext x
  exact TensorRepresentatives.CM.section_value F N φ x

variable {G : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F → Type*} [∀ v, Group (G v)]
  (K : ∀ v, Subgroup (G v))
  (ρ : ∀ v, G v →* (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N ≃ₗ[ℂ]
    RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N))
  (hρ : ∀ᶠ v in cofinite, ∀ g ∈ K v, ρ v g (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) = RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v)

theorem kernel_invariant (g : RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K) (x : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F N)
    (hx : RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz F N x = 0) :
    RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz F N (RepresentationTheory.Theta.Adelic.TensorProjective.Restricted.action (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) K ρ hρ g x) = 0 := by
  apply Subtype.ext
  exact EvaluationKernel.CM.action_preserves_zero F N K ρ hρ g x
    (congrArg Subtype.val hx)

def functionAction : RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K →*
    (RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F N ≃ₗ[ℂ] RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F N) :=
  SurjectiveRepresentationDescent.CM.action (RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz F N)
    (TensorRepresentatives.CM.sectionMap F N) (section_identity F N)
    (RepresentationTheory.Theta.Adelic.TensorProjective.Restricted.action (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) K ρ hρ) (kernel_invariant F N K ρ hρ)

theorem intertwines (g : RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K) (x : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F N) :
    functionAction F N K ρ hρ g (RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz F N x) =
      RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz F N (RepresentationTheory.Theta.Adelic.TensorProjective.Restricted.action (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) K ρ hρ g x) :=
  SurjectiveRepresentationDescent.CM.intertwines (RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz F N)
    (TensorRepresentatives.CM.sectionMap F N) (section_identity F N)
    (RepresentationTheory.Theta.Adelic.TensorProjective.Restricted.action (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) K ρ hρ) (kernel_invariant F N K ρ hρ) g x

theorem pure_value (g : RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K)
    (f : ∀ v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F, RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N)
    (hf : ∀ᶠ v in cofinite, f v = RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) (x : Fin N → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :
    (functionAction F N K ρ hρ g (RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz F N (RepresentationTheory.Theta.Adelic.TensorProjective.Restricted.pure (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) f hf))).val x =
      ∏ᶠ v, (ρ v (g v) (f v)).val (fun i => x i v) := by
  rw [intertwines, RestrictedTensorExpansion.CM.action_pure]
  exact RepresentationTheory.Theta.Adelic.Evaluation.finiteSchwartzFunction_pure F N _ _ x

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FunctionAction.CM

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FunctionAction.CM.FunctionalDescent

/-! Restricted products of normalized local functionals descend to
actual adelic Schwartz functions. No injectivity of tensor evaluation is
assumed: its kernel is annihilated by the actual local functionals. -/

open scoped Classical _root_.NumberField
open Filter
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz
open OAI.RepresentationTheory.Theta.Adelic.Evaluation OAI.RepresentationTheory.Theta.Adelic.TensorProjective.Restricted

variable (F : Type) [Field F] [NumberField F] (N : ℕ)
  (ell : ∀ v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F, RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N →ₗ[ℂ] ℂ)
  (hell : ∀ᶠ v in cofinite, ell v (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) = 1)

def tensorFunctional : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F N →ₗ[ℂ] ℂ :=
  RepresentationTheory.Theta.Adelic.TensorProjective.Evaluation.evaluate (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) ell hell

theorem pure_value
    (f : ∀ v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F, RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N)
    (hf : ∀ᶠ v in cofinite, f v = RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) :
    tensorFunctional F N ell hell (RepresentationTheory.Theta.Adelic.TensorProjective.Restricted.pure (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) f hf) = ∏ᶠ v, ell v (f v) :=
  RepresentationTheory.Theta.Adelic.TensorProjective.Evaluation.evaluate_pure (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) ell hell f hf

theorem kernel_zero (t : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F N) (ht : RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz F N t = 0) :
    tensorFunctional F N ell hell t = 0 := by
  obtain ⟨r, c, f, hf, hrep⟩ := RestrictedTensorExpansion.CM.expansion (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) t
  have hz (x : Fin N → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :
      ∑ j, c j * ∏ᶠ v, (f j v).val (fun i => x i v) = 0 := by
    have h := congrArg (fun φ : RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F N => φ.val x) ht
    change RepresentationTheory.Theta.Adelic.Evaluation.finiteSchwartzFunction F N t x = 0 at h
    rw [hrep] at h
    simpa only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      RepresentationTheory.Theta.Adelic.Evaluation.finiteSchwartzFunction_pure] using h
  let T (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) := (ell v).smulRight (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v)
  have hT : ∀ᶠ v in cofinite, T v (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) = RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v := by
    filter_upwards [hell] with v hv
    change ell v (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) • RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v = _
    rw [hv, one_smul]
  have h := ProductRelations.CM.relation_preserved F N T hT c f hf hz 0
  have he (j : Fin r) (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) : (T v (f j v)).val (fun i => (0 : Fin N → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) i v) =
      ell v (f j v) := by
    change ell v (f j v) * (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v).val 0 = _
    rw [RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum_zero, mul_one]
  simp_rw [he] at h
  rw [hrep]
  simpa only [map_sum, map_smul, smul_eq_mul, pure_value] using h

def functionFunctional : RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F N →ₗ[ℂ] ℂ :=
  (tensorFunctional F N ell hell).comp (TensorRepresentatives.CM.sectionMap F N)

theorem intertwines (t : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F N) :
    functionFunctional F N ell hell (RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz F N t) = tensorFunctional F N ell hell t := by
  have hz : RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz F N
      (t - TensorRepresentatives.CM.sectionMap F N (RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz F N t)) = 0 := by
    rw [map_sub, section_identity, sub_self]
  have h := kernel_zero F N ell hell _ hz
  rw [map_sub] at h
  exact (sub_eq_zero.mp h).symm

theorem function_pure
    (f : ∀ v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F, RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N)
    (hf : ∀ᶠ v in cofinite, f v = RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) :
    functionFunctional F N ell hell (RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz F N (RepresentationTheory.Theta.Adelic.TensorProjective.Restricted.pure (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) f hf)) =
      ∏ᶠ v, ell v (f v) :=
  (intertwines F N ell hell _).trans (pure_value F N ell hell f hf)

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FunctionAction.CM.FunctionalDescent

end

end OAI
