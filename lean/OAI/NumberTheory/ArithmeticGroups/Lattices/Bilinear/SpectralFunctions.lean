import OAI.NumberTheory.ArithmeticGroups.Lattices.PolynomialSpectralFunctions

/-! # Spectral Functions -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Bilinear.SpectralFunctions.Construction

noncomputable section

/-! Multiplicative functions of positive eigenvalues preserve a
bilinear operation; functions turning products into sums give derivations. -/

variable {k L ι : Type*} [Field k] [AddCommGroup L] [Module k L] [Fintype ι]

theorem bilinear_preserver_eigenproduct
    (B : L →ₗ[k] L →ₗ[k] L) (g : L →ₗ[k] L)
    (hB : ∀ x y, g (B x y) = B (g x) (g y))
    (x y : L) (a c : k) (hx : g x = a • x) (hy : g y = c • y) :
    g (B x y) = (a * c) • B x y := by
  rw [hB, hx, hy]
  simp only [map_smul, LinearMap.smul_apply, smul_smul, mul_comm]

theorem bilinear_spectral_function_preserves
    (B : L →ₗ[k] L →ₗ[k] L) (b : Module.Basis ι k L) (g h : L →ₗ[k] L)
    (w : ι → k) (ψ : k → k) (hg : ∀ i, g (b i) = w i • b i)
    (hh : ∀ i, h (b i) = ψ (w i) • b i)
    (hB : ∀ x y, g (B x y) = B (g x) (g y))
    (hψ : ∀ i j, ψ (w i * w j) = ψ (w i) * ψ (w j)) :
    ∀ x y, h (B x y) = B (h x) (h y) := by
  have heq : B.compr₂ h = B.compl₁₂ h h := by
    apply b.ext
    intro i
    apply b.ext
    intro j
    change h (B (b i) (b j)) = B (h (b i)) (h (b j))
    rw [PolynomialSpectralFunctions.Construction.eigenvalue_function_on_eigenvector b g h w ψ hg hh _ (w i * w j)
      (bilinear_preserver_eigenproduct B g hB _ _ _ _ (hg i) (hg j)),
      hψ, hh, hh]
    simp only [map_smul, LinearMap.smul_apply, smul_smul, mul_comm]
  intro x y
  exact congrArg (fun C : L →ₗ[k] L →ₗ[k] L => C x y) heq

theorem bilinear_spectral_function_derivation
    (B : L →ₗ[k] L →ₗ[k] L) (b : Module.Basis ι k L) (g D : L →ₗ[k] L)
    (w : ι → k) (ψ : k → k) (hg : ∀ i, g (b i) = w i • b i)
    (hD : ∀ i, D (b i) = ψ (w i) • b i)
    (hB : ∀ x y, g (B x y) = B (g x) (g y))
    (hψ : ∀ i j, ψ (w i * w j) = ψ (w i) + ψ (w j)) :
    ∀ x y, D (B x y) = B (D x) y + B x (D y) := by
  have heq : B.compr₂ D = B.compl₁₂ D LinearMap.id + B.compl₁₂ LinearMap.id D := by
    apply b.ext
    intro i
    apply b.ext
    intro j
    change D (B (b i) (b j)) = B (D (b i)) (b j) + B (b i) (D (b j))
    rw [PolynomialSpectralFunctions.Construction.eigenvalue_function_on_eigenvector b g D w ψ hg hD _ (w i * w j)
      (bilinear_preserver_eigenproduct B g hB _ _ _ _ (hg i) (hg j)),
      hψ, hD, hD]
    simp only [map_smul, LinearMap.smul_apply, add_smul]
  intro x y
  exact congrArg (fun C : L →ₗ[k] L →ₗ[k] L => C x y) heq

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Bilinear.SpectralFunctions.Construction
