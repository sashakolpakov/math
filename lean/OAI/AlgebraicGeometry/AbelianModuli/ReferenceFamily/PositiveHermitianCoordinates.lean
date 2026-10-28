import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Positive Hermitian Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PositiveHermitianCoordinates

noncomputable section

/-! A positive Hermitian form supplies its own orthonormal coordinates.
The conclusion is purely linear and retains the given form exactly. -/

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]

theorem exists_positiveHermitian_coordinates
    (F : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (hsym : ∀ x y, F y x = star (F x y))
    (hpos : ∀ x : V, x ≠ 0 → 0 < (F x x).re)
    (n : ℕ) (hdim : Module.finrank ℂ V = n) :
    ∃ e : V ≃ₗ[ℂ] (Fin n → ℂ), ∀ x y : V,
      F x y = ∑ i, e x i * star (e y i) := by
  let core : InnerProductSpace.Core ℂ V := {
    inner x y := F y x
    conj_inner_symm x y := (hsym x y).symm
    re_inner_nonneg x := by
      by_cases hx : x = 0
      · rw [hx, map_zero]
        exact le_rfl
      · exact (hpos x hx).le
    add_left x y z := (F z).map_add x y
    smul_left x y r := (F y).map_smulₛₗ r x
    definite x hx := by
      by_contra hn
      have h := hpos x hn
      rw [hx, Complex.zero_re] at h
      exact (lt_irrefl 0) h }
  let : InnerProductSpace.Core ℂ V := core
  let : NormedAddCommGroup V := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := V)
  let : InnerProductSpace ℂ V := InnerProductSpace.ofCore core.toCore
  let b : OrthonormalBasis (Fin n) ℂ V :=
    (stdOrthonormalBasis ℂ V).reindex (finCongr hdim)
  let e : V ≃ₗ[ℂ] (Fin n → ℂ) := b.toBasis.equivFun
  refine ⟨e, ?_⟩
  intro x y
  have he (v : V) (i : Fin n) : e v i = inner ℂ (b i) v :=
    (b.coe_toBasis_repr_apply v i).trans (b.repr_apply_apply v i)
  have h : (∑ i, inner ℂ y (b i) * inner ℂ (b i) x) = F x y :=
    b.sum_inner_mul_inner y x
  apply h.symm.trans
  apply Finset.sum_congr rfl
  intro i _
  rw [← inner_conj_symm y (b i), ← he y i, ← he x i]
  exact mul_comm _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PositiveHermitianCoordinates
