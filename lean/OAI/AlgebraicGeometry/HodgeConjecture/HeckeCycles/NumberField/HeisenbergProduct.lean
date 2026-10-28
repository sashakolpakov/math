import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NumberField.HeisenbergFamily
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.TraceHeisenberg
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NumberField.FiniteSymplectic

/-! # Heisenberg Product -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NumberField.HeisenbergProduct.CM

noncomputable section

/-! Exact finite-product evaluation of local Heisenberg translates,
including the actual finite additive character and the half-translation. -/

open scoped Classical _root_.NumberField
open Filter Function
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.Evaluation

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NumberField.FiniteSymplectic.CM

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

local instance (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) : CharZero (v.adicCompletion F) := RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.completionCharZero F (.inr v)

theorem evaluation_rat (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) (r : ℚ) :
    FiniteSymplectic.CM.evaluation F v (algebraMap ℚ (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) r) = algebraMap ℚ (v.adicCompletion F) r := by
  have h : (FiniteSymplectic.CM.evaluation F v).comp (algebraMap ℚ (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F)) =
      algebraMap ℚ (v.adicCompletion F) := Subsingleton.elim _ _
  exact congrArg (fun f : ℚ →+* v.adicCompletion F => f r) h

def phaseArgument (z : (Fin N ⊕ Fin N) → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (x : Fin N → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :
    RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F := ∑ i, z (.inr i) * (x i - algebraMap ℚ (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (1 / 2) * z (.inl i))

theorem phaseArgument_local (z : (Fin N ⊕ Fin N) → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F)
    (x : Fin N → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) :
    FiniteSymplectic.CM.evaluation F v (phaseArgument F N z x) =
      ∑ i, z (.inr i) v * (x i v - z (.inl i) v / 2) := by
  have hh : algebraMap ℚ (v.adicCompletion F) (1 / 2) = (2 : v.adicCompletion F)⁻¹ := by
    norm_num
  simp only [phaseArgument, map_sum, map_mul, map_sub, evaluation_rat]
  rw [hh]
  apply Finset.sum_congr rfl
  intro i _
  change z (.inr i) v * (x i v - (2 : v.adicCompletion F)⁻¹ * z (.inl i) v) = _
  rw [div_eq_mul_inv, mul_comm (2 : v.adicCompletion F)⁻¹]

variable (ψ : AddChar (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ) (hu : ∀ t, ‖ψ t‖ = 1) (hc : Continuous ψ)

theorem product (z : (Fin N ⊕ Fin N) → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F)
    (f : ∀ v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F, RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N)
    (hf : ∀ᶠ v in cofinite, f v = RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) (x : Fin N → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :
    (∏ᶠ v, (HeisenbergFamily.CM.Family.localOperator F N ψ hu hc z v (f v)).val
      (fun i => x i v)) =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg (RepresentationTheory.Weil.AdelicSplitting.FiniteCharacterProduct.Construction.finiteAdelicCharacter F ψ)
        (fun i => z (.inr i)) (fun i => z (.inl i))
        (fun y => ∏ᶠ v, (f v).val (fun i => y i v)) x := by
  have hphase : (fun v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F =>
      RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ (.inr v)
        (∑ i, z (.inr i) v * (x i v - z (.inl i) v / 2))) =
      (fun v => RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ (.inr v) (phaseArgument F N z x v)) := by
    funext v
    exact congrArg (RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ (.inr v)) (phaseArgument_local F N z x v).symm
  have hs := RepresentationTheory.Theta.Adelic.TensorProjective.Evaluation.evaluation_finite_support
    (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) (RepresentationTheory.Theta.Adelic.Evaluation.localEvaluation F N (fun i => x i - z (.inl i)))
    (RepresentationTheory.Theta.Adelic.Evaluation.vacuum_evaluation_eventually_one F N (fun i => x i - z (.inl i))) f hf
  change HasFiniteMulSupport (fun v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F =>
    (f v).val (fun i => x i v - z (.inl i) v)) at hs
  change (∏ᶠ v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F,
    RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ (.inr v)
      (∑ i, z (.inr i) v * (x i v - z (.inl i) v / 2)) *
      (f v).val (fun i => x i v - z (.inl i) v)) = _
  rw [show (fun v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F =>
    RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ (.inr v)
      (∑ i, z (.inr i) v * (x i v - z (.inl i) v / 2)) *
      (f v).val (fun i => x i v - z (.inl i) v)) =
    (fun v => RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ (.inr v) (phaseArgument F N z x v) *
      (f v).val (fun i => x i v - z (.inl i) v)) from
        funext (fun v => congrArg (fun a => a * (f v).val (fun i => x i v - z (.inl i) v))
          (congrFun hphase v))]
  rw [finprod_mul_distrib
    (LocalCharacter.CM.finite_support F ψ hc hu (phaseArgument F N z x)) hs,
    LocalCharacter.CM.finite_product F ψ hc hu]
  rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NumberField.HeisenbergProduct.CM
