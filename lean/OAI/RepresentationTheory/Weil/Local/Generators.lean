import OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic

/-! # Generators -/

namespace OAI.RepresentationTheory.Weil.Local.Generators.Construction

noncomputable section

section

/-! Concrete symplectic generators and algebraic normalization checks. -/

open _root_.MeasureTheory
open scoped BigOperators

def leviSymplectic {k : Type} [Field k] {n : ℕ}
    (A : FunctionsMetaplectic.Construction.GeneralLinear k n) : FunctionsMetaplectic.Construction.Symplectic k n := by
  refine ⟨Matrix.fromBlocks (↑A) 0 0 (↑(A⁻¹) : Matrix (Fin n) (Fin n) k).transpose, ?_⟩
  rw [SymplecticGroup.fromBlocks_mem_iff]
  simp [← Matrix.transpose_mul]

def quadraticSymplectic {k : Type} [Field k] {n : ℕ}
    (B : FunctionsMetaplectic.Construction.SymmetricMatrix k n) : FunctionsMetaplectic.Construction.Symplectic k n := by
  refine ⟨Matrix.fromBlocks 1 0 B.val 1, ?_⟩
  rw [SymplecticGroup.fromBlocks_mem_iff]
  simp [B.property.eq]

def weylSymplectic (k : Type) [Field k] (n : ℕ) : FunctionsMetaplectic.Construction.Symplectic k n := by
  refine ⟨Matrix.fromBlocks 0 1 (-1) 0, ?_⟩
  rw [SymplecticGroup.fromBlocks_mem_iff]
  simp

theorem leviSymplectic_matrix {k : Type} [Field k] {n : ℕ}
    (A : FunctionsMetaplectic.Construction.GeneralLinear k n) :
    (leviSymplectic A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k) =
      Matrix.fromBlocks (↑A) 0 0 (↑(A⁻¹) : Matrix (Fin n) (Fin n) k).transpose := rfl

theorem quadraticSymplectic_matrix {k : Type} [Field k] {n : ℕ}
    (B : FunctionsMetaplectic.Construction.SymmetricMatrix k n) :
    (quadraticSymplectic B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k) =
      Matrix.fromBlocks 1 0 B.val 1 := rfl

theorem weylSymplectic_matrix (k : Type) [Field k] (n : ℕ) :
    (weylSymplectic k n : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k) =
      Matrix.fromBlocks 0 1 (-1) 0 := rfl

theorem quadraticOperator_norm {k : Type} [Field k] {n : ℕ}
    (ψ : AddChar k ℂ) (hψ : ∀ t : k, ‖ψ t‖ = 1)
    (B : Matrix (Fin n) (Fin n) k) (f : FunctionsMetaplectic.Construction.Position k n → ℂ) (x : FunctionsMetaplectic.Construction.Position k n) :
    ‖FunctionsMetaplectic.Construction.quadraticOperator ψ B f x‖ = ‖f x‖ := by
  rw [FunctionsMetaplectic.Construction.quadraticOperator_apply, norm_mul, hψ, one_mul]

theorem quadraticOperator_comp {k : Type} [Field k] {n : ℕ}
    (ψ : AddChar k ℂ) (B C : Matrix (Fin n) (Fin n) k)
    (f : FunctionsMetaplectic.Construction.Position k n → ℂ) :
    FunctionsMetaplectic.Construction.quadraticOperator ψ B (FunctionsMetaplectic.Construction.quadraticOperator ψ C f) = FunctionsMetaplectic.Construction.quadraticOperator ψ (B + C) f := by
  funext x
  simp only [FunctionsMetaplectic.Construction.quadraticOperator_apply, ← mul_assoc, ← ψ.map_add_eq_mul]
  congr 2
  simp [FunctionsMetaplectic.Construction.quadratic, mul_add, add_mul, Finset.sum_add_distrib, add_div]

theorem substitutionOperator_comp {k : Type} [Field k] {n : ℕ}
    (A B : FunctionsMetaplectic.Construction.GeneralLinear k n) (f : FunctionsMetaplectic.Construction.Position k n → ℂ) :
    FunctionsMetaplectic.Construction.substitutionOperator A (FunctionsMetaplectic.Construction.substitutionOperator B f) = FunctionsMetaplectic.Construction.substitutionOperator (A * B) f := by
  funext x
  simp only [FunctionsMetaplectic.Construction.substitutionOperator_apply, Matrix.mulVec_mulVec,
    mul_inv_rev, Units.val_mul]

def symplecticPairing {k : Type} [Field k] {n : ℕ}
    (v w : FunctionsMetaplectic.Construction.PhaseSpace k n) : k :=
  ∑ i, (v (Sum.inr i) * w (Sum.inl i) - v (Sum.inl i) * w (Sum.inr i))

/-- The Heisenberg central cocycle is derived from the coordinate formula. -/
theorem heisenbergFunction_comp {k : Type} [Field k] [CharZero k] {n : ℕ}
    (ψ : AddChar k ℂ) (v w : FunctionsMetaplectic.Construction.PhaseSpace k n) (f : FunctionsMetaplectic.Construction.Position k n → ℂ) :
    FunctionsMetaplectic.Construction.heisenbergFunction ψ v (FunctionsMetaplectic.Construction.heisenbergFunction ψ w f) =
      ψ (symplecticPairing v w / 2) • FunctionsMetaplectic.Construction.heisenbergFunction ψ (v + w) f := by
  funext x
  simp only [FunctionsMetaplectic.Construction.heisenbergFunction, Pi.smul_apply, smul_eq_mul, Pi.add_apply,
    ← mul_assoc, ← ψ.map_add_eq_mul]
  have hphase :
      (∑ i, v (Sum.inr i) * (x i - v (Sum.inl i) / 2)) +
        (∑ i, w (Sum.inr i) * (x i - v (Sum.inl i) - w (Sum.inl i) / 2)) =
      symplecticPairing v w / 2 +
        ∑ i, (v (Sum.inr i) + w (Sum.inr i)) *
          (x i - (v (Sum.inl i) + w (Sum.inl i)) / 2) := by
    simp only [symplecticPairing, Finset.sum_div, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hphase]
  congr 2
  funext i
  ring

variable (k : Type) [NormedField k] [LocallyCompactSpace k]
  [MeasurableSpace k] [BorelSpace k]

theorem leviFactor_norm {n : ℕ} (ψ : AddChar k ℂ) (A : FunctionsMetaplectic.Construction.GeneralLinear k n)
    (hdet : FunctionsMetaplectic.Construction.gaussianIntegral k ψ (FunctionsMetaplectic.Construction.determinantUnit k A) ≠ 0)
    (hone : FunctionsMetaplectic.Construction.gaussianIntegral k ψ 1 ≠ 0) :
    ‖FunctionsMetaplectic.Construction.leviFactor k ψ A‖ = (Real.sqrt (FunctionsMetaplectic.Construction.localModulus k (FunctionsMetaplectic.Construction.determinantUnit k A)))⁻¹ := by
  have hs : 0 < Real.sqrt (FunctionsMetaplectic.Construction.localModulus k (FunctionsMetaplectic.Construction.determinantUnit k A)) :=
    Real.sqrt_pos.2 (FunctionsMetaplectic.Construction.localModulus_pos k _)
  simp only [FunctionsMetaplectic.Construction.leviFactor, norm_mul, norm_div, FunctionsMetaplectic.Construction.gaussianIndex_norm k ψ _ hdet,
    FunctionsMetaplectic.Construction.gaussianIndex_norm k ψ _ hone, div_self one_ne_zero, one_mul,
    norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]

theorem index_ratio_eighth_power (ψ : AddChar k ℂ) (a : k)
    (ha : FunctionsMetaplectic.Construction.gaussianIndex k ψ a ^ 8 = 1) (h1 : FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 ^ 8 = 1) :
    (FunctionsMetaplectic.Construction.gaussianIndex k ψ a / FunctionsMetaplectic.Construction.gaussianIndex k ψ 1) ^ 8 = 1 := by
  rw [div_pow, ha, h1, div_self one_ne_zero]

end

/-! Momentum rescaling and the resulting automorphism of the symplectic group. -/

open _root_.Matrix

def phaseScaleMatrix {k : Type} [Field k] (n : ℕ) (c : k) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k :=
  fromBlocks 1 0 0 (c • 1)

theorem phaseScaleMatrix_mul {k : Type} [Field k] (n : ℕ) (c d : k) :
    phaseScaleMatrix n c * phaseScaleMatrix n d = phaseScaleMatrix n (c * d) := by
  simp [phaseScaleMatrix, fromBlocks_multiply, smul_smul, mul_comm]

theorem phaseScaleMatrix_one {k : Type} [Field k] (n : ℕ) :
    phaseScaleMatrix n (1 : k) = 1 := by simp [phaseScaleMatrix]

theorem phaseScaleMatrix_inverse {k : Type} [Field k] (n : ℕ) (c : k) (hc : c ≠ 0) :
    phaseScaleMatrix n c * phaseScaleMatrix n c⁻¹ = 1 := by
  rw [phaseScaleMatrix_mul, mul_inv_cancel₀ hc, phaseScaleMatrix_one]

theorem phaseScaleMatrix_form {k : Type} [Field k] (n : ℕ) (c : k) :
    phaseScaleMatrix n c * J (Fin n) k * (phaseScaleMatrix n c)ᵀ = c • J (Fin n) k := by
  simp [phaseScaleMatrix, J, fromBlocks_multiply, fromBlocks_transpose,
    fromBlocks_smul]

def phaseRescaleSymplectic {k : Type} [Field k] (n : ℕ) (c : k) (hc : c ≠ 0) :
    FunctionsMetaplectic.Construction.Symplectic k n →* FunctionsMetaplectic.Construction.Symplectic k n where
  toFun g := ⟨phaseScaleMatrix n c * g.val * phaseScaleMatrix n c⁻¹, by
    apply SymplecticGroup.mem_iff.mpr
    calc
      _ = phaseScaleMatrix n c * g.val *
          (phaseScaleMatrix n c⁻¹ * J (Fin n) k * (phaseScaleMatrix n c⁻¹)ᵀ) *
          g.valᵀ * (phaseScaleMatrix n c)ᵀ := by
        simp only [transpose_mul, Matrix.mul_assoc]
      _ = c⁻¹ • (phaseScaleMatrix n c * (g.val * J (Fin n) k * g.valᵀ) *
          (phaseScaleMatrix n c)ᵀ) := by
        rw [phaseScaleMatrix_form]
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = J (Fin n) k := by
        rw [SymplecticGroup.mem_iff.mp g.property, phaseScaleMatrix_form,
          smul_smul, inv_mul_cancel₀ hc, one_smul]⟩
  map_one' := by
    apply Subtype.ext
    change phaseScaleMatrix n c * 1 * phaseScaleMatrix n c⁻¹ = 1
    rw [mul_one, phaseScaleMatrix_inverse n c hc]
  map_mul' g h := by
    apply Subtype.ext
    change phaseScaleMatrix n c * (g.val * h.val) * phaseScaleMatrix n c⁻¹ =
      (phaseScaleMatrix n c * g.val * phaseScaleMatrix n c⁻¹) *
        (phaseScaleMatrix n c * h.val * phaseScaleMatrix n c⁻¹)
    have hinv : phaseScaleMatrix n c⁻¹ * phaseScaleMatrix n c = 1 := by
      rw [phaseScaleMatrix_mul, inv_mul_cancel₀ hc, phaseScaleMatrix_one]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (phaseScaleMatrix n c⁻¹) (phaseScaleMatrix n c), hinv, one_mul]

theorem phaseRescaleSymplectic_action {k : Type} [Field k] {n : ℕ} (c : k) (hc : c ≠ 0)
    (g : FunctionsMetaplectic.Construction.Symplectic k n) (v : FunctionsMetaplectic.Construction.PhaseSpace k n) :
    FunctionsMetaplectic.Construction.symplecticAction (phaseRescaleSymplectic n c hc g) (phaseScaleMatrix n c *ᵥ v) =
      phaseScaleMatrix n c *ᵥ FunctionsMetaplectic.Construction.symplecticAction g v := by
  change (phaseScaleMatrix n c * g.val * phaseScaleMatrix n c⁻¹) *ᵥ
    (phaseScaleMatrix n c *ᵥ v) = phaseScaleMatrix n c *ᵥ (g.val *ᵥ v)
  have hinv : phaseScaleMatrix n c⁻¹ * phaseScaleMatrix n c = 1 := by
    rw [phaseScaleMatrix_mul, inv_mul_cancel₀ hc, phaseScaleMatrix_one]
  rw [mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hinv, mul_one, mulVec_mulVec]

theorem phaseScaleMatrix_surjective {k : Type} [Field k] (n : ℕ) (c : k) (hc : c ≠ 0) :
    Function.Surjective (phaseScaleMatrix n c).mulVec := by
  intro v
  refine ⟨phaseScaleMatrix n c⁻¹ *ᵥ v, ?_⟩
  rw [mulVec_mulVec, phaseScaleMatrix_inverse n c hc, one_mulVec]

theorem phaseScaleMatrix_apply_inl {k : Type} [Field k] {n : ℕ}
    (c : k) (v : FunctionsMetaplectic.Construction.PhaseSpace k n) (i : Fin n) : (phaseScaleMatrix n c *ᵥ v) (Sum.inl i) = v (Sum.inl i) := by
  simp [phaseScaleMatrix, fromBlocks_mulVec]

theorem phaseScaleMatrix_apply_inr {k : Type} [Field k] {n : ℕ}
    (c : k) (v : FunctionsMetaplectic.Construction.PhaseSpace k n) (i : Fin n) : (phaseScaleMatrix n c *ᵥ v) (Sum.inr i) = c * v (Sum.inr i) := by
  simp [phaseScaleMatrix, fromBlocks_mulVec, Matrix.smul_mulVec]

end

end OAI.RepresentationTheory.Weil.Local.Generators.Construction
