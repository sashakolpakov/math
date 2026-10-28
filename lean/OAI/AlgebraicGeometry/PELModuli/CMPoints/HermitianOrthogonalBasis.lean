import OAI.AlgebraicGeometry.PELModuli.CMPoints.HermitianDiagonalization

/-! # Hermitian Orthogonal Basis -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.HermitianOrthogonalBasis

noncomputable section

/-! Hermitian diagonalization with a prescribed non-null vector. The
form need not be anisotropic; the nontrivial coefficient involution
provides the polarization identity needed for induction. -/

open scoped Classical
open _root_.Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem hermitian_add_right (σ : K ≃+* K) (B : V →ₗ[K] (V → K))
    (hB : ∀ x y, B x y = σ (B y x)) (x y z : V) :
    B x (y + z) = B x y + B x z := by
  rw [hB x (y + z), B.map_add]
  change σ (B y x + B z x) = _
  rw [map_add, ← hB x y, ← hB x z]

theorem hermitian_smul_right (σ : K ≃+* K) (B : V →ₗ[K] (V → K))
    (hB : ∀ x y, B x y = σ (B y x)) (a : K) (x y : V) :
    B x (a • y) = σ a * B x y := by
  rw [hB x (a • y), B.map_smul]
  change σ (a * B y x) = _
  rw [map_mul, ← hB x y]

theorem hermitian_self_zero_implies_zero (σ : K ≃+* K) (a : K) (ha : σ a ≠ a)
    (B : V →ₗ[K] (V → K)) (hB : ∀ x y, B x y = σ (B y x))
    (hzero : ∀ x, B x x = 0) : B = 0 := by
  apply LinearMap.ext
  intro x
  funext y
  have h₁ : B x y + B y x = 0 := by
    have h := hzero (x + y)
    rw [B.map_add] at h
    change B x (x + y) + B y (x + y) = 0 at h
    simpa only [hermitian_add_right σ B hB, hzero, zero_add, add_zero] using h
  have h₂ : a * B x y + σ a * B y x = 0 := by
    have h := hzero (a • x + y)
    rw [B.map_add] at h
    change B (a • x) (a • x + y) + B y (a • x + y) = 0 at h
    rw [hermitian_add_right σ B hB, hermitian_add_right σ B hB,
      hzero, hzero, zero_add, add_zero, hermitian_smul_right σ B hB, B.map_smul] at h
    exact h
  have h₃ : (a - σ a) * B x y = 0 := by
    linear_combination h₂ - σ a * h₁
  exact (mul_eq_zero.mp h₃).resolve_left (sub_ne_zero.mpr ha.symm)

theorem exists_hermitian_orthogonal_basis [FiniteDimensional K V]
    (σ : K ≃+* K) (a : K) (ha : σ a ≠ a)
    (B : V →ₗ[K] (V → K)) (hB : ∀ x y, B x y = σ (B y x)) :
    ∃ b : Basis (Fin (finrank K V)) K V,
      Pairwise (fun i j => B (b i) (b j) = 0) := by
  suffices ∀ d, finrank K V = d →
      ∃ b : Basis (Fin d) K V, Pairwise (fun i j => B (b i) (b j) = 0) by
    exact this _ rfl
  intro d hd
  induction d generalizing V with
  | zero => exact ⟨basisOfFinrankZero hd, fun i => Fin.elim0 i⟩
  | succ d ih =>
    by_cases hz : B = 0
    · subst B
      exact ⟨(Module.finBasis K V).reindex (finCongr hd), fun _ _ _ => rfl⟩
    have hex : ∃ x, B x x ≠ 0 := by
      by_contra! h
      exact hz (hermitian_self_zero_implies_zero σ a ha B hB h)
    obtain ⟨x, hx⟩ := hex
    have hx0 : x ≠ 0 := by
      intro h
      subst x
      simp at hx
    have hd' : finrank K (HermitianDiagonalization.orthogonalFunctional B x).ker = d := by
      have h := Submodule.finrank_add_eq_of_isCompl
        (HermitianDiagonalization.span_isCompl_orthogonalFunctional B x hx).symm
      rw [finrank_span_singleton hx0, hd] at h
      omega
    obtain ⟨b, hb⟩ := ih (V := (HermitianDiagonalization.orthogonalFunctional B x).ker)
      (HermitianDiagonalization.restrictFirstOrthogonal B x) (fun y z => hB y.val z.val) hd'
    refine ⟨HermitianDiagonalization.extendOrthogonalBasis B x hx b,
      HermitianDiagonalization.extendOrthogonalBasis_orthogonal B x hx ?_ b hb⟩
    intro y z
    rw [hB y z]
    exact map_eq_zero σ

theorem exists_hermitian_orthogonal_basis_with_first [FiniteDimensional K V]
    (σ : K ≃+* K) (a : K) (ha : σ a ≠ a)
    (B : V →ₗ[K] (V → K)) (hB : ∀ x y, B x y = σ (B y x))
    (x : V) (hx : B x x ≠ 0) (n : ℕ) (hd : finrank K V = n + 1) :
    ∃ b : Basis (Fin (n + 1)) K V, b 0 = x ∧
      Pairwise (fun i j => B (b i) (b j) = 0) := by
  have hx0 : x ≠ 0 := by
    intro h
    subst x
    simp at hx
  have hd' : finrank K (HermitianDiagonalization.orthogonalFunctional B x).ker = n := by
    have h := Submodule.finrank_add_eq_of_isCompl
      (HermitianDiagonalization.span_isCompl_orthogonalFunctional B x hx).symm
    rw [finrank_span_singleton hx0, hd] at h
    omega
  obtain ⟨b, hb⟩ := exists_hermitian_orthogonal_basis σ a ha
    (HermitianDiagonalization.restrictFirstOrthogonal B x) (fun y z => hB y.val z.val)
  subst n
  refine ⟨HermitianDiagonalization.extendOrthogonalBasis B x hx b, HermitianDiagonalization.extendOrthogonalBasis_zero B x hx b,
    HermitianDiagonalization.extendOrthogonalBasis_orthogonal B x hx ?_ b hb⟩
  intro y z
  rw [hB y z]
  exact map_eq_zero σ

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.HermitianOrthogonalBasis
