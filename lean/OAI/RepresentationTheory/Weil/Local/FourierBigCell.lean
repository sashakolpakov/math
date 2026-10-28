import OAI.RepresentationTheory.Weil.Local.PolynomialMatrixAvoidance
import OAI.RepresentationTheory.Weil.Local.NonarchimedeanCover

/-! # Fourier Big Cell -/

namespace OAI.RepresentationTheory.Weil.Local.FourierBigCell.Construction

noncomputable section

/-! The symplectic domain with invertible Fourier block meets every finite collection of left translates. -/

open _root_.Matrix

variable {k : Type} [Field k] {n : ℕ}

def fourierBigCell (k : Type) [Field k] (n : ℕ) : Set (FunctionsMetaplectic.Construction.Symplectic k n) :=
  {g | g.val.toBlocks₁₂.det ≠ 0}

theorem weylSymplectic_inv_matrix :
    ((Generators.Construction.weylSymplectic k n)⁻¹).val = Matrix.fromBlocks 0 (-1) 1 0 := by
  rw [SymplecticGroup.coe_inv]
  simp [Generators.Construction.weylSymplectic, Matrix.J, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_neg]

theorem symplectic_exists_fourier_block_shift (g : FunctionsMetaplectic.Construction.Symplectic k n) :
    ∃ X : Matrix (Fin n) (Fin n) k, X.IsSymm ∧
      (g.val.toBlocks₁₂ + X * g.val.toBlocks₂₂).det ≠ 0 := by
  obtain ⟨X, hX⟩ := GenerationSymplectic.Construction.symplectic_exists_upper_bigCell (g * (Generators.Construction.weylSymplectic k n)⁻¹)
  refine ⟨X.val, X.property, ?_⟩
  change IsUnit (((GenerationSymplectic.Construction.upperSymplectic X).val * (g.val * ((Generators.Construction.weylSymplectic k n)⁻¹).val)).toBlocks₁₁).det at hX
  rw [weylSymplectic_inv_matrix, ← Matrix.fromBlocks_toBlocks g.val] at hX
  simpa [GenerationSymplectic.Construction.upperSymplectic, Matrix.fromBlocks_multiply] using hX.ne_zero

theorem fourierBigCell_finite_left_translates [Infinite k] (F : Finset (FunctionsMetaplectic.Construction.Symplectic k n)) :
    ∃ x : FunctionsMetaplectic.Construction.Symplectic k n, ∀ g ∈ F, x * g ∈ fourierBigCell k n := by
  obtain ⟨X, hX, hall⟩ := PolynomialMatrixAvoidance.Construction.exists_symmetric_all_determinants_ne_zero F
    (fun g => g.val.toBlocks₁₂) (fun g => g.val.toBlocks₂₂)
    (fun g _ => symplectic_exists_fourier_block_shift g)
  refine ⟨GenerationSymplectic.Construction.upperSymplectic ⟨X, hX⟩, ?_⟩
  intro g hg
  change (((GenerationSymplectic.Construction.upperSymplectic ⟨X, hX⟩).val * g.val).toBlocks₁₂).det ≠ 0
  rw [← Matrix.fromBlocks_toBlocks g.val]
  simpa [GenerationSymplectic.Construction.upperSymplectic, Matrix.fromBlocks_multiply] using hall g hg

theorem oscillator_fourierBigCell_finite_left_translates
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hnd : ¬ DiscreteTopology k) (n : ℕ)
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1) (hc : Continuous (fun t => ψ t))
    (hn : ∃ t : k, ψ t ≠ 1) (F : Finset (FunctionsMetaplectic.Construction.Oscillator k n ψ)) :
    ∃ x : FunctionsMetaplectic.Construction.Oscillator k n ψ, ∀ g ∈ F,
      OscillatorProjection.Construction.oscillatorProjection k n ψ (x * g) ∈ fourierBigCell k n := by
  classical
  obtain ⟨x, hx⟩ := fourierBigCell_finite_left_translates (F.image (OscillatorProjection.Construction.oscillatorProjection k n ψ))
  obtain ⟨a, ha⟩ := NonarchimedeanCover.Construction.nonarchimedean_metaplecticProjection_surjective hnd n ψ hu hc hn x
  refine ⟨a.val, ?_⟩
  intro g hg
  rw [map_mul]
  change FunctionsMetaplectic.Construction.metaplecticProjection k n ψ a * OscillatorProjection.Construction.oscillatorProjection k n ψ g ∈ fourierBigCell k n
  rw [ha]
  exact hx _ (Finset.mem_image_of_mem _ hg)

end

end OAI.RepresentationTheory.Weil.Local.FourierBigCell.Construction
