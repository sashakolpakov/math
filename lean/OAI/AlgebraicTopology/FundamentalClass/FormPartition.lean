import OAI.AlgebraicTopology.FundamentalClass.TopEvaluation
import OAI.Analysis.DifferentialForms.Manifold.FunctionMultiplication

/-! # Form Partition -/

namespace OAI.AlgebraicTopology.FundamentalClass.FormPartition.IntegrationConstruction

noncomputable section

/-! Genuine smooth cutoffs decompose supported forms and every linear
functional on those forms by a finite partition of unity. -/

open Set
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {n : ℕ}

def weightForm (ρ : M → ℝ) (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n →ₗ[ℂ] Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n :=
  Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.smulByFunction (fun x => (ρ x : ℂ))
    (Complex.ofRealCLM.contDiff.contMDiff.comp hρ)

theorem weightForm_apply (ρ : M → ℝ) (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) (x : M) :
    (weightForm ρ hρ form).val x = (ρ x : ℂ) • form.val x := rfl

theorem weightForm_inChart (ρ : M → ℝ) (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) (e : OpenPartialHomeomorph M E) (y : E)
    (v : Fin n → E) :
    (weightForm ρ hρ form).val.inChart e y v =
      (ρ (e.symm y) : ℂ) * form.val.inChart e y v := rfl

theorem weightForm_zero_of_notMem_tsupport (ρ : M → ℝ)
    (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ) (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n)
    (x : M) (hx : x ∉ tsupport ρ) : (weightForm ρ hρ form).val x = 0 := by
  rw [weightForm_apply, image_eq_zero_of_notMem_tsupport hx, Complex.ofReal_zero]
  exact zero_smul ℂ (form.val x)

theorem sum_weightForm {ι : Type} [Fintype ι] (K : Set M)
    (ρ : SmoothPartitionOfUnity ι 𝓘(ℝ, E) M K)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) (hform : ∀ x, x ∉ K → form.val x = 0) :
    ∑ i, weightForm (ρ i) (ρ i).contMDiff form = form := by
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  change Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.eval x (∑ i, weightForm (ρ i) (ρ i).contMDiff form) = form.val x
  rw [map_sum]
  change ∑ i, (ρ i x : ℂ) • form.val x = form.val x
  rw [← Finset.sum_smul]
  by_cases hx : x ∈ K
  · have hs : ∑ i, ρ i x = 1 := by simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one hx
    have hs' : ∑ i, (ρ i x : ℂ) = 1 := by exact_mod_cast hs
    rw [hs', one_smul]
  · rw [hform x hx, smul_zero]

theorem linearFunctional_partition {ι : Type} [Fintype ι] (K : Set M)
    (ρ : SmoothPartitionOfUnity ι 𝓘(ℝ, E) M K)
    (L : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n →ₗ[ℂ] ℂ)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) (hform : ∀ x, x ∉ K → form.val x = 0) :
    L form = ∑ i, L (weightForm (ρ i) (ρ i).contMDiff form) := by
  rw [← map_sum, sum_weightForm K ρ form hform]

end

end OAI.AlgebraicTopology.FundamentalClass.FormPartition.IntegrationConstruction
