import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RestrictedPositions
import OAI.RepresentationTheory.Theta.Adelic.CompactSupport

/-! # Adelic Local Factorization -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.AdelicLocalFactorization.CM

noncomputable section

section

/-! ThetaCycle: every actual finite adelic Schwartz function has a finite local
factorization, with the integral vacuum outside finitely many places. -/

open scoped Classical _root_.NumberField
open Filter
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

def finiteAdelicPositionHomeomorph :
    (Fin N → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) ≃ₜ
      RestrictedProduct (fun v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F => Fin N → v.adicCompletion F)
        (fun v => {x | ∀ i, x i ∈ v.adicCompletionIntegers F}) cofinite :=
  RestrictedPositions.CM.restrictedPositionHomeomorph
    (fun v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun v => Valued.isOpen_integer (v.adicCompletion F))

theorem finite_adelic_position_lattice_compact (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) :
    IsCompact {x : Fin N → v.adicCompletion F | ∀ i, x i ∈ v.adicCompletionIntegers F} := by
  simpa only [RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finitePositionLattice, Set.pi, Set.mem_univ, forall_true_left] using!
    RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finitePositionLattice_compact F N v

theorem finite_adelic_position_lattice_open (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) :
    IsOpen {x : Fin N → v.adicCompletion F | ∀ i, x i ∈ v.adicCompletionIntegers F} := by
  simpa only [RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finitePositionLattice, Set.pi, Set.mem_univ, forall_true_left] using!
    (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finitePositionLattice_clopen F N v).isOpen

theorem finite_adelic_local_factorization (p : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F)
    (φ : RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F N) :
    ∃ (S : Finset (RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F)) (n : ℕ) (c : Fin n → ℂ)
      (ψ : Fin n → (v : S) → Analysis.Schwartz.TensorDecomposition.Constructions.SchwartzBruhat (Fin N → v.val.adicCompletion F)),
      p ∈ S ∧ ∀ x : Fin N → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F,
        φ.val x = if ∀ v, v ∉ S → ∀ i, x i v ∈ v.adicCompletionIntegers F then
          ∑ j : Fin n, c j * ∏ v : S, (ψ j v).val (fun i => x i v.val) else 0 := by
  let h := finiteAdelicPositionHomeomorph F N
  let f : Analysis.Schwartz.TensorDecomposition.Constructions.SchwartzBruhat _ :=
    ⟨φ.val ∘ h.symm, φ.property.1.comp_continuous h.symm.continuous,
      φ.property.2.comp_homeomorph h.symm⟩
  obtain ⟨S, n, c, ψ, hp, he⟩ := Analysis.Schwartz.TensorDecomposition.Constructions.finite_local_factorization
    (fun v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F => Fin N → v.adicCompletion F)
    (fun v => {x | ∀ i, x i ∈ v.adicCompletionIntegers F})
    (finite_adelic_position_lattice_compact F N) (finite_adelic_position_lattice_open F N)
    (fun v => ⟨0, fun _ => (v.adicCompletionIntegers F).zero_mem⟩) p f
  refine ⟨S, n, c, ψ, hp, fun x => ?_⟩
  have hx := he (h x)
  change φ.val (h.symm (h x)) = _ at hx
  rw [h.symm_apply_apply] at hx
  exact hx

end

/-! ThetaCycle: the native restricted tensor evaluation represents every actual
finite adelic Schwartz function. This is an existence theorem for the full
function space, without a tensor-factorization hypothesis on the input. -/

open scoped Classical _root_.NumberField
open Filter
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz
open OAI.RepresentationTheory.Theta.Adelic.Evaluation OAI.RepresentationTheory.Theta.Adelic.Evaluation.AdelicLocalConstancy
open OAI.RepresentationTheory.Theta.Adelic.TensorProjective.Restricted

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

def localFactorFamily (S : Finset (RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F))
    (ψ : (v : S) → Analysis.Schwartz.TensorDecomposition.Constructions.SchwartzBruhat (Fin N → v.val.adicCompletion F))
    (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N :=
  if hv : v ∈ S then
    ⟨(ψ ⟨v, hv⟩).val, RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.compact_locallyConstant_mem (ψ ⟨v, hv⟩).property.1
      (ψ ⟨v, hv⟩).property.2⟩
  else RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v

theorem local_factor_family_inside (S : Finset (RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F))
    (ψ : (v : S) → Analysis.Schwartz.TensorDecomposition.Constructions.SchwartzBruhat (Fin N → v.val.adicCompletion F))
    (v : S) : (localFactorFamily F N S ψ v.val).val = (ψ v).val := by
  simp only [localFactorFamily, dite_eq_left v.property]

theorem local_factor_family_outside (S : Finset (RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F))
    (ψ : (v : S) → Analysis.Schwartz.TensorDecomposition.Constructions.SchwartzBruhat (Fin N → v.val.adicCompletion F))
    (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) (hv : v ∉ S) : localFactorFamily F N S ψ v = RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v :=
  dite_eq_right hv

theorem local_factor_family_restricted (S : Finset (RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F))
    (ψ : (v : S) → Analysis.Schwartz.TensorDecomposition.Constructions.SchwartzBruhat (Fin N → v.val.adicCompletion F)) :
    ∀ᶠ v in cofinite, localFactorFamily F N S ψ v = RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v := by
  filter_upwards [show ∀ᶠ v in cofinite, v ∉ S from by simp] with v hv
  exact local_factor_family_outside F N S ψ v hv

def localFactorTensor (S : Finset (RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F))
    (ψ : (v : S) → Analysis.Schwartz.TensorDecomposition.Constructions.SchwartzBruhat (Fin N → v.val.adicCompletion F)) :
    RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F N :=
  RepresentationTheory.Theta.Adelic.TensorProjective.Restricted.pure (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) (localFactorFamily F N S ψ) (local_factor_family_restricted F N S ψ)

theorem local_factor_tensor_evaluation (S : Finset (RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F))
    (ψ : (v : S) → Analysis.Schwartz.TensorDecomposition.Constructions.SchwartzBruhat (Fin N → v.val.adicCompletion F))
    (x : Fin N → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :
    RepresentationTheory.Theta.Adelic.Evaluation.finiteSchwartzFunction F N (localFactorTensor F N S ψ) x =
      if ∀ v, v ∉ S → ∀ i, x i v ∈ v.adicCompletionIntegers F then
        ∏ v : S, (ψ v).val (fun i => x i v.val) else 0 := by
  rw [localFactorTensor, RepresentationTheory.Theta.Adelic.Evaluation.finiteSchwartzFunction_pure,
    RepresentationTheory.Theta.Adelic.Evaluation.AdelicLocalConstancy.pure_product_decomposition F N _ (local_factor_family_restricted F N S ψ) S
      (local_factor_family_outside F N S ψ)]
  by_cases hx : ∀ v, v ∉ S → ∀ i, x i v ∈ v.adicCompletionIntegers F
  · rw [ite_eq_left hx, (LocallyConstant.charFn_eq_one ℂ x (RepresentationTheory.Theta.Adelic.Evaluation.AdelicLocalConstancy.integralOutside_clopen F N S)).mpr hx,
      one_mul]
    rw [← Finset.prod_coe_sort S]
    apply Finset.prod_congr rfl
    intro v _
    exact congrFun (local_factor_family_inside F N S ψ v) (fun i => x i v.val)
  · rw [ite_eq_right hx, (LocallyConstant.charFn_eq_zero ℂ x (RepresentationTheory.Theta.Adelic.Evaluation.AdelicLocalConstancy.integralOutside_clopen F N S)).mpr hx,
      zero_mul]

theorem finite_schwartz_evaluation_surjective (p : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) :
    Function.Surjective (RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz F N) := by
  intro φ
  obtain ⟨S, n, c, ψ, _, hdec⟩ := finite_adelic_local_factorization F N p φ
  refine ⟨∑ j : Fin n, c j • localFactorTensor F N S (ψ j), ?_⟩
  apply Subtype.ext
  funext x
  change RepresentationTheory.Theta.Adelic.Evaluation.finiteSchwartzFunction F N (∑ j : Fin n, c j • localFactorTensor F N S (ψ j)) x = φ.val x
  rw [map_sum, Finset.sum_apply]
  simp only [map_smul, Pi.smul_apply, smul_eq_mul, local_factor_tensor_evaluation]
  rw [hdec x]
  split_ifs with hx
  · rfl
  · simp only [mul_zero, Finset.sum_const_zero]

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.AdelicLocalFactorization.CM
