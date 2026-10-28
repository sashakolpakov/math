import OAI.RepresentationTheory.Theta.Kernel.Analysis
import OAI.RepresentationTheory.Theta.Kernel.Calculus

/-! # Factorization -/

namespace OAI.RepresentationTheory.Theta.Kernel.Factorization

noncomputable section

open scoped BigOperators

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- DerivativeFactorization's direct-sum proposition, quantified over its displayed data. -/
def DerivativeFactorizationInput (ι κ : Type*) [Fintype ι] [Fintype κ] : Prop :=
  ∀ (Z₁ : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (Z₂ : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix κ) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Sum ι κ)),
    Z.matrix = Matrix.fromBlocks Z₁.matrix 0 0 Z₂.matrix →
    ∀ (ψ : Definitions.DerivativeFactorization.Input ι) (χ : Definitions.DerivativeFactorization.Input κ), ∃ φ : Definitions.DerivativeFactorization.Input (Sum ι κ),
      (∀ a, φ.1 a = ψ.1 (fun i => a (Sum.inl i)) * χ.1 (fun j => a (Sum.inr j))) ∧
      (∀ z₁ z₂, Definitions.DerivativeFactorization.completed φ Z (Sum.elim z₁ z₂) = Definitions.DerivativeFactorization.completed ψ Z₁ z₁ * Definitions.DerivativeFactorization.completed χ Z₂ z₂)

/-- The two-factor TensorDecomposition proposition in the rational splitting's coordinates.
The scalar coefficients are retained, as in TensorDecomposition's specification. -/
def TensorDecompositionInput (ι κ : Type*) : Prop :=
  ∀ φ : Definitions.DerivativeFactorization.Input (Sum ι κ), ∃ (n : ℕ) (c : Fin n → ℂ)
    (ψ : Fin n → Definitions.DerivativeFactorization.Input ι) (χ : Fin n → Definitions.DerivativeFactorization.Input κ),
    ∀ a, φ.1 a = ∑ i, c i *
      (ψ i).1 (fun j => a (Sum.inl j)) * (χ i).1 (fun j => a (Sum.inr j))

def scaleInput (c : ℂ) (φ : Definitions.DerivativeFactorization.Input ι) : Definitions.DerivativeFactorization.Input ι :=
  ⟨fun a => c * φ.1 a, (IsLocallyConstant.const c).mul φ.2.1, φ.2.2.mul_left⟩

omit [Fintype ι] [Fintype κ] in
lemma tensor_decomposition (h_TensorDecomposition : TensorDecompositionInput ι κ) (φ : Definitions.DerivativeFactorization.Input (Sum ι κ)) :
    ∃ (n : ℕ) (ψ : Fin n → Definitions.DerivativeFactorization.Input ι) (χ : Fin n → Definitions.DerivativeFactorization.Input κ),
      ∀ a, φ.1 a = ∑ i,
        (ψ i).1 (fun j => a (Sum.inl j)) * (χ i).1 (fun j => a (Sum.inr j)) := by
  obtain ⟨n, c, ψ, χ, h⟩ := h_TensorDecomposition φ
  exact ⟨n, fun i => scaleInput (c i) (ψ i), χ, h⟩

lemma completed_sum (h_GaussianConvergence : Analysis.GaussianConvergenceInput ι) (φ : Definitions.DerivativeFactorization.Input ι)
    (n : ℕ) (ψ : Fin n → Definitions.DerivativeFactorization.Input ι) (h : ∀ a, φ.1 a = ∑ i, (ψ i).1 a)
    (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) :
    Definitions.DerivativeFactorization.completed φ Z = fun z => ∑ i, Definitions.DerivativeFactorization.completed (ψ i) Z z := by
  funext z
  have heq : Definitions.DerivativeFactorization.theta φ Z.matrix z = ∑ i, Definitions.DerivativeFactorization.theta (ψ i) Z.matrix z := by
    simp only [Definitions.DerivativeFactorization.theta, h, Finset.sum_mul]
    exact Summable.tsum_finsetSum (fun i _ => (Analysis.adelic_analysis h_GaussianConvergence (ψ i) Z).1 z)
  simp only [Definitions.DerivativeFactorization.completed, heq, Finset.mul_sum]

lemma completed_hessian_sum (h_GaussianConvergence : Analysis.GaussianConvergenceInput ι) (φ : Definitions.DerivativeFactorization.Input ι)
    (n : ℕ) (ψ : Fin n → Definitions.DerivativeFactorization.Input ι) (h : ∀ a, φ.1 a = ∑ i, (ψ i).1 a)
    (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (v : Fin 2 → (ι → ℂ)) :
    iteratedFDeriv ℂ 2 (Definitions.DerivativeFactorization.completed φ Z) 0 v =
      ∑ i, iteratedFDeriv ℂ 2 (Definitions.DerivativeFactorization.completed (ψ i) Z) 0 v := by
  rw [completed_sum h_GaussianConvergence φ n ψ h Z,
    iteratedFDeriv_fun_sum_apply
      (fun i _ => ((Analysis.adelic_analysis h_GaussianConvergence (ψ i) Z).2.of_le (by simp)).contDiffAt)]
  exact _root_.sum_apply _ _ _

def leftProjection : (Sum ι κ → ℂ) →L[ℂ] (ι → ℂ) :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (Sum.inl i))

def rightProjection : (Sum ι κ → ℂ) →L[ℂ] (κ → ℂ) :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (Sum.inr i))

lemma completed_tensor (h_DerivativeFactorization : DerivativeFactorizationInput ι κ)
    (Z₁ : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (Z₂ : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix κ) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Sum ι κ))
    (hZ : Z.matrix = Matrix.fromBlocks Z₁.matrix 0 0 Z₂.matrix)
    (φ : Definitions.DerivativeFactorization.Input (Sum ι κ)) (ψ : Definitions.DerivativeFactorization.Input ι) (χ : Definitions.DerivativeFactorization.Input κ)
    (hφ : ∀ a, φ.1 a = ψ.1 (fun i => a (Sum.inl i)) * χ.1 (fun j => a (Sum.inr j))) :
    Definitions.DerivativeFactorization.completed φ Z = fun z =>
      Definitions.DerivativeFactorization.completed ψ Z₁ (leftProjection z) * Definitions.DerivativeFactorization.completed χ Z₂ (rightProjection z) := by
  obtain ⟨φ', hφ', h⟩ := h_DerivativeFactorization Z₁ Z₂ Z hZ ψ χ
  have heq : φ = φ' := Subtype.ext (funext (fun a => (hφ a).trans (hφ' a).symm))
  subst φ'
  funext z
  have hz : Sum.elim (leftProjection z) (rightProjection z) = z := by
    funext i; cases i <;> rfl
  simpa only [hz] using h (leftProjection z) (rightProjection z)

lemma mixed_completed (h_GaussianConvergence₁ : Analysis.GaussianConvergenceInput ι) (h_GaussianConvergence₂ : Analysis.GaussianConvergenceInput κ)
    (h_DerivativeFactorization : DerivativeFactorizationInput ι κ)
    (Z₁ : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (Z₂ : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix κ) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Sum ι κ))
    (hZ : Z.matrix = Matrix.fromBlocks Z₁.matrix 0 0 Z₂.matrix)
    (φ : Definitions.DerivativeFactorization.Input (Sum ι κ)) (ψ : Definitions.DerivativeFactorization.Input ι) (χ : Definitions.DerivativeFactorization.Input κ)
    (hφ : ∀ a, φ.1 a = ψ.1 (fun i => a (Sum.inl i)) * χ.1 (fun j => a (Sum.inr j)))
    (u : ι → ℂ) (v : κ → ℂ) :
    iteratedFDeriv ℂ 2 (Definitions.DerivativeFactorization.completed φ Z) 0 ![Sum.elim u 0, Sum.elim 0 v] =
      fderiv ℂ (Definitions.DerivativeFactorization.completed ψ Z₁) 0 u * fderiv ℂ (Definitions.DerivativeFactorization.completed χ Z₂) 0 v := by
  rw [completed_tensor h_DerivativeFactorization Z₁ Z₂ Z hZ φ ψ χ hφ]
  have hf : ContDiff ℂ 2 (Definitions.DerivativeFactorization.completed ψ Z₁) := (Analysis.adelic_analysis h_GaussianConvergence₁ ψ Z₁).2.of_le (by simp)
  have hg : ContDiff ℂ 2 (Definitions.DerivativeFactorization.completed χ Z₂) := (Analysis.adelic_analysis h_GaussianConvergence₂ χ Z₂).2.of_le (by simp)
  exact Calculus.mixed_hessian (leftProjection (ι := ι) (κ := κ))
    (rightProjection (ι := ι) (κ := κ)) (Definitions.DerivativeFactorization.completed ψ Z₁) (Definitions.DerivativeFactorization.completed χ Z₂) hf hg
    (Sum.elim u (0 : κ → ℂ)) (Sum.elim (0 : ι → ℂ) v) rfl rfl

lemma mixed_completed_reverse (h_GaussianConvergence₁ : Analysis.GaussianConvergenceInput ι) (h_GaussianConvergence₂ : Analysis.GaussianConvergenceInput κ)
    (h_DerivativeFactorization : DerivativeFactorizationInput ι κ)
    (Z₁ : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (Z₂ : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix κ) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Sum ι κ))
    (hZ : Z.matrix = Matrix.fromBlocks Z₁.matrix 0 0 Z₂.matrix)
    (φ : Definitions.DerivativeFactorization.Input (Sum ι κ)) (ψ : Definitions.DerivativeFactorization.Input ι) (χ : Definitions.DerivativeFactorization.Input κ)
    (hφ : ∀ a, φ.1 a = ψ.1 (fun i => a (Sum.inl i)) * χ.1 (fun j => a (Sum.inr j)))
    (u : ι → ℂ) (v : κ → ℂ) :
    iteratedFDeriv ℂ 2 (Definitions.DerivativeFactorization.completed φ Z) 0 ![Sum.elim 0 v, Sum.elim u 0] =
      fderiv ℂ (Definitions.DerivativeFactorization.completed ψ Z₁) 0 u * fderiv ℂ (Definitions.DerivativeFactorization.completed χ Z₂) 0 v := by
  rw [completed_tensor h_DerivativeFactorization Z₁ Z₂ Z hZ φ ψ χ hφ]
  have hf : ContDiff ℂ 2 (Definitions.DerivativeFactorization.completed ψ Z₁) := (Analysis.adelic_analysis h_GaussianConvergence₁ ψ Z₁).2.of_le (by simp)
  have hg : ContDiff ℂ 2 (Definitions.DerivativeFactorization.completed χ Z₂) := (Analysis.adelic_analysis h_GaussianConvergence₂ χ Z₂).2.of_le (by simp)
  have h := Calculus.mixed_hessian (rightProjection (ι := ι) (κ := κ))
    (leftProjection (ι := ι) (κ := κ)) (Definitions.DerivativeFactorization.completed χ Z₂) (Definitions.DerivativeFactorization.completed ψ Z₁) hg hf
    (Sum.elim (0 : ι → ℂ) v) (Sum.elim u (0 : κ → ℂ)) rfl rfl
  have hLu : leftProjection (Sum.elim u (0 : κ → ℂ)) = u := rfl
  have hRv : rightProjection (Sum.elim (0 : ι → ℂ) v) = v := rfl
  rw [hLu, hRv] at h
  simpa only [mul_comm] using h

end

end OAI.RepresentationTheory.Theta.Kernel.Factorization
