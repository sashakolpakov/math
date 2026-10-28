import OAI.AlgebraicGeometry.PELModuli.CMPoints.RationalNegativeLine
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-! # Hermitian Diagonalization -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.HermitianDiagonalization

noncomputable section

section

/-! Orthogonal diagonalization with a prescribed first vector. Only
linearity in the first argument, symmetric orthogonality, and anisotropy
are used; in particular this applies to Hermitian forms. -/

open scoped Classical
open _root_.Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def orthogonalFunctional (B : V →ₗ[K] (V → K)) (x : V) : V →ₗ[K] K :=
  (LinearMap.proj x).comp B

theorem span_isCompl_orthogonalFunctional (B : V →ₗ[K] (V → K))
    (x : V) (hx : B x x ≠ 0) :
    IsCompl (K ∙ x) (orthogonalFunctional B x).ker := by
  constructor
  · rw [Submodule.disjoint_def]
    intro y hy hy'
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    have ha : a * B x x = 0 := by
      simpa [orthogonalFunctional] using hy'
    rw [(mul_eq_zero.mp ha).resolve_right hx, zero_smul]
  · exact codisjoint_iff.mpr
      (LinearMap.span_singleton_sup_ker_eq_top (orthogonalFunctional B x) hx)

def restrictFirstOrthogonal (B : V →ₗ[K] (V → K)) (x : V) :
    (orthogonalFunctional B x).ker →ₗ[K] ((orthogonalFunctional B x).ker → K) where
  toFun y z := B y.val z.val
  map_add' y z := by ext t; exact congrFun (B.map_add y.val z.val) t.val
  map_smul' a y := by ext t; exact congrFun (B.map_smul a y.val) t.val

def extendOrthogonalBasis (B : V →ₗ[K] (V → K)) (x : V) (hx : B x x ≠ 0)
    {n : ℕ} (b : Basis (Fin n) K (orthogonalFunctional B x).ker) :
    Basis (Fin (n + 1)) K V :=
  Basis.mkFinCons x b
    (by
      intro a y hy heq
      have he : a * B x x = 0 := by
        have h := congrArg (orthogonalFunctional B x) heq
        simpa [orthogonalFunctional, show B y x = 0 from hy] using h
      exact (mul_eq_zero.mp he).resolve_right hx)
    (by
      intro y
      refine ⟨-B y x / B x x, ?_⟩
      change B (y + (-B y x / B x x) • x) x = 0
      simp [div_mul_cancel₀ _ hx])

theorem extendOrthogonalBasis_zero (B : V →ₗ[K] (V → K)) (x : V)
    (hx : B x x ≠ 0) {n : ℕ}
    (b : Basis (Fin n) K (orthogonalFunctional B x).ker) :
    extendOrthogonalBasis B x hx b 0 = x := by
  rw [extendOrthogonalBasis, Basis.coe_mkFinCons]
  rfl

theorem extendOrthogonalBasis_orthogonal (B : V →ₗ[K] (V → K)) (x : V)
    (hx : B x x ≠ 0) (hsym : ∀ y z, B y z = 0 ↔ B z y = 0)
    {n : ℕ} (b : Basis (Fin n) K (orthogonalFunctional B x).ker)
    (hb : Pairwise (fun i j => B (b i).val (b j).val = 0)) :
    Pairwise (fun i j =>
      B (extendOrthogonalBasis B x hx b i) (extendOrthogonalBasis B x hx b j) = 0) := by
  rw [extendOrthogonalBasis, Basis.coe_mkFinCons]
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j <;> intro hij
  · exact (hij rfl).elim
  · exact (hsym _ _).mpr (b j).prop
  · exact (b i).prop
  · exact hb (ne_of_apply_ne Fin.succ hij)

theorem exists_anisotropic_orthogonal_basis [FiniteDimensional K V]
    (B : V →ₗ[K] (V → K))
    (hsym : ∀ x y, B x y = 0 ↔ B y x = 0)
    (hani : ∀ x, B x x = 0 → x = 0) :
    ∃ b : Basis (Fin (finrank K V)) K V,
      Pairwise (fun i j => B (b i) (b j) = 0) := by
  suffices ∀ d, finrank K V = d →
      ∃ b : Basis (Fin d) K V, Pairwise (fun i j => B (b i) (b j) = 0) by
    exact this _ rfl
  intro d hd
  induction d generalizing V with
  | zero =>
    refine ⟨basisOfFinrankZero hd, ?_⟩
    intro i
    exact Fin.elim0 i
  | succ d ih =>
    let i : Fin (finrank K V) := ⟨0, by omega⟩
    let x : V := Module.finBasis K V i
    have hx0 : x ≠ 0 := (Module.finBasis K V).ne_zero i
    have hx : B x x ≠ 0 := fun h => hx0 (hani x h)
    have hd' : finrank K (orthogonalFunctional B x).ker = d := by
      have heq := Submodule.finrank_add_eq_of_isCompl
        (span_isCompl_orthogonalFunctional B x hx).symm
      rw [finrank_span_singleton hx0, hd] at heq
      omega
    obtain ⟨b, hb⟩ := ih (V := (orthogonalFunctional B x).ker)
      (restrictFirstOrthogonal B x)
      (fun y z => hsym y.val z.val)
      (fun y hy => Subtype.ext (hani y.val hy)) hd'
    exact ⟨extendOrthogonalBasis B x hx b,
      extendOrthogonalBasis_orthogonal B x hx hsym b hb⟩

theorem exists_anisotropic_orthogonal_basis_with_first [FiniteDimensional K V]
    (B : V →ₗ[K] (V → K))
    (hsym : ∀ x y, B x y = 0 ↔ B y x = 0)
    (hani : ∀ x, B x x = 0 → x = 0)
    (x : V) (hx0 : x ≠ 0) (n : ℕ) (hd : finrank K V = n + 1) :
    ∃ b : Basis (Fin (n + 1)) K V, b 0 = x ∧
      Pairwise (fun i j => B (b i) (b j) = 0) := by
  have hx : B x x ≠ 0 := fun h => hx0 (hani x h)
  have hd' : finrank K (orthogonalFunctional B x).ker = n := by
    have heq := Submodule.finrank_add_eq_of_isCompl
      (span_isCompl_orthogonalFunctional B x hx).symm
    rw [finrank_span_singleton hx0, hd] at heq
    omega
  obtain ⟨b, hb⟩ := exists_anisotropic_orthogonal_basis
    (restrictFirstOrthogonal B x)
    (fun y z => hsym y.val z.val)
    (fun y hy => Subtype.ext (hani y.val hy))
  subst n
  exact ⟨extendOrthogonalBasis B x hx b,
    extendOrthogonalBasis_zero B x hx b,
    extendOrthogonalBasis_orthogonal B x hx hsym b hb⟩

end

/-! Every anisotropic rational Hermitian ball has an orthogonal rational
basis whose first line is negative at the distinguished embedding. -/

open scoped Classical

open _root_.Module

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E]

def matrixHermitianFirstLinear (H : Matrix (Fin 3) (Fin 3) E) :
    (Fin 3 → E) →ₗ[E] ((Fin 3 → E) → E) where
  toFun := AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.matrixHermitian H
  map_add' x y := by
    ext z
    simp [AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.matrixHermitian, add_mul, Finset.sum_add_distrib]
  map_smul' a x := by
    ext y
    simp [AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.matrixHermitian, Finset.mul_sum, mul_assoc]

omit [Algebra ℚ E] in
theorem matrixHermitian_conjugate_swap (H : Matrix (Fin 3) (Fin 3) E)
    (hH : ∀ i j, H i j = NumberField.IsCMField.complexConj E (H j i))
    (x y : Fin 3 → E) :
    AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.matrixHermitian H x y =
      NumberField.IsCMField.complexConj E (AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.matrixHermitian H y x) := by
  simp only [AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.matrixHermitian, map_sum, map_mul,
    NumberField.IsCMField.complexConj_apply_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [← hH i j]
  ring

omit [Algebra ℚ E] in
theorem matrixHermitian_orthogonal_symm (H : Matrix (Fin 3) (Fin 3) E)
    (hH : ∀ i j, H i j = NumberField.IsCMField.complexConj E (H j i))
    (x y : Fin 3 → E) :
    AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.matrixHermitian H x y = 0 ↔ AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.matrixHermitian H y x = 0 := by
  rw [matrixHermitian_conjugate_swap H hH x y]
  exact map_eq_zero (NumberField.IsCMField.complexConj E)

theorem exists_rational_orthogonal_negative_basis
    (σ : E →ₐ[ℚ] ℂ) (H : Matrix (Fin 3) (Fin 3) E)
    (hH : ∀ i j, H i j = NumberField.IsCMField.complexConj E (H j i))
    (hani : ∀ x : Fin 3 → E, AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.matrixHermitian H x x = 0 → x = 0)
    (w : Fin 3 → ℂ) (hw : (AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian σ.toRingHom H w w).re < 0) :
    ∃ b : Basis (Fin 3) E (Fin 3 → E),
      Pairwise (fun i j => AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.matrixHermitian H (b i) (b j) = 0) ∧
      (AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian σ.toRingHom H
        (fun i => σ (b 0 i)) (fun i => σ (b 0 i))).re < 0 := by
  obtain ⟨v, hv0, hv⟩ := RationalNegativeLine.exists_rational_negative_vector σ H w hw
  obtain ⟨b, hb, ho⟩ := exists_anisotropic_orthogonal_basis_with_first
    (matrixHermitianFirstLinear H)
    (matrixHermitian_orthogonal_symm H hH) hani v hv0 2 (by simp)
  exact ⟨b, ho, by simpa [hb] using hv⟩

theorem matrixHermitian_embedding (σ : E →ₐ[ℚ] ℂ)
    (H : Matrix (Fin 3) (Fin 3) E) (x y : Fin 3 → E) :
    σ (AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.matrixHermitian H x y) =
      AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian σ.toRingHom H (fun i => σ (x i)) (fun i => σ (y i)) := by
  have hc (z : E) : σ (NumberField.IsCMField.complexConj E z) = star (σ z) :=
    NumberField.IsCMField.complexEmbedding_complexConj E σ.toRingHom z
  simp [AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.matrixHermitian, AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian, hc]

omit [Algebra ℚ E] in
theorem matrixHermitian_diagonal_fixed (H : Matrix (Fin 3) (Fin 3) E)
    (hH : ∀ i j, H i j = NumberField.IsCMField.complexConj E (H j i))
    (x : Fin 3 → E) :
    NumberField.IsCMField.complexConj E (AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.matrixHermitian H x x) =
      AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.matrixHermitian H x x :=
  (matrixHermitian_conjugate_swap H hH x x).symm

omit [Algebra ℚ E] in
theorem matrixHermitian_diagonal_ne_zero (H : Matrix (Fin 3) (Fin 3) E)
    (hani : ∀ x : Fin 3 → E, AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.matrixHermitian H x x = 0 → x = 0)
    (b : Basis (Fin 3) E (Fin 3 → E)) (i : Fin 3) :
    AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.matrixHermitian H (b i) (b i) ≠ 0 :=
  fun h => b.ne_zero i (hani (b i) h)

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.HermitianDiagonalization
