import OAI.RepresentationTheory.Theta.Kernel.IntrinsicSchwartz
import OAI.RepresentationTheory.Theta.DerivativeFactorizationPrerequisites

/-! # Intrinsic Decomposition -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicDecomposition.Intrinsic

noncomputable section

/-! The full TensorDecomposition proposition gives a finite tensor expansion of an actual
native input, after the explicit finite-adelic block homeomorphism. -/

open scoped _root_.NumberField Classical BigOperators

open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.Evaluation OAI.RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz OAI.RepresentationTheory.Theta.Kernel.IntrinsicSchwartz.Intrinsic

variable (F : Type) [Field F] [NumberField F]

local instance : LocallyCompactSpace (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :=
  (Weil.AdelicSplitting.IntegralAdeles.Construction.isCompact_finiteIntegralRing F).locallyCompactSpace_of_mem_nhds_of_addGroup
    ((Weil.AdelicSplitting.IntegralAdeles.Construction.isOpen_finiteIntegralRing F).mem_nhds (Weil.AdelicSplitting.IntegralAdeles.Construction.finiteIntegralRing F).zero_mem)

local instance : T2Space (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :=
  inferInstanceAs (T2Space (RestrictedProduct
    (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite))

local instance : TotallyDisconnectedSpace (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) := by
  constructor
  exact isTotallyDisconnected_of_image RestrictedProduct.continuous_coe.continuousOn
    (fun x y h => RestrictedProduct.ext _ _ (congrFun h))
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)

def twoBlocks (n : ℕ) : (Fin (n + n) → Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) ≃ₜ
    (Fin 2 → Fin n → Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :=
  (IntrinsicSchwartz.Intrinsic.splitPositions n n).trans Homeomorph.finTwoArrow.symm

theorem finite_tensor_expansion
    (hTensorDecomposition : DerivativeFactorizationPrerequisites.Prerequisites.TensorDecomposition.Statement.{0, 0, 0, 0})
    (n : ℕ) (f : Adelic.FiniteSchwartz.finiteSchwartz F (n + n)) :
    ∃ (k : ℕ) (c : Fin k → ℂ) (a b : Fin k → Adelic.FiniteSchwartz.finiteSchwartz F n),
      ∀ x : Fin (n + n) → Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F,
        Adelic.Evaluation.finiteSchwartzFunction F (n + n) f x =
          ∑ j : Fin k, c j *
            (Adelic.Evaluation.finiteSchwartzFunction F n (a j) (fun i => x (Fin.castAdd n i)) *
             Adelic.Evaluation.finiteSchwartzFunction F n (b j) (fun i => x (Fin.natAdd n i))) := by
  let φ := Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz F (n + n) f
  let e := twoBlocks F n
  let ψ : DerivativeFactorizationPrerequisites.Prerequisites.TensorDecomposition.SchwartzBruhat (Fin 2 → Fin n → Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :=
    ⟨φ.val ∘ e.symm, φ.property.1.comp_continuous e.symm.continuous,
      φ.property.2.comp_homeomorph e.symm⟩
  obtain ⟨k, c, p, hp⟩ := hTensorDecomposition.1 (fun _ : Fin 2 => Fin n → Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) ψ
  let q (j : Fin k) (r : Fin 2) : Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F n :=
    ⟨(p j r).val, (p j r).property⟩
  refine ⟨k, c, (fun j => IntrinsicSchwartz.Intrinsic.liftFunction F n (q j 0)),
    (fun j => IntrinsicSchwartz.Intrinsic.liftFunction F n (q j 1)), ?_⟩
  intro x
  have he := hp (e x)
  simp only [ψ, Function.comp_apply, Homeomorph.symm_apply_apply] at he
  change φ.val x = _
  rw [he]
  apply Finset.sum_congr rfl
  intro j _
  rw [IntrinsicSchwartz.Intrinsic.liftFunction_value, IntrinsicSchwartz.Intrinsic.liftFunction_value]
  simp only [Fin.prod_univ_two]
  rfl

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicDecomposition.Intrinsic
