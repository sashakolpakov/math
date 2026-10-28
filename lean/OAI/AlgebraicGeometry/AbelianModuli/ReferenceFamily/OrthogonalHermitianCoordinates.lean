import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PositiveHermitianCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.HermitianMatrixForm
import Mathlib.LinearAlgebra.Projection

/-! # Orthogonal Hermitian Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.OrthogonalHermitianCoordinates

noncomputable section

section

/-! Complementary positive and negative orthogonal subspaces give an
explicit Hermitian coordinate equivalence with a signed diagonal form. -/

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]

theorem exists_orthogonalHermitian_coordinates
    (F : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hsym : ∀ x y, F y x = star (F x y))
    (P Q : Submodule ℂ V) (hPQ : IsCompl P Q)
    (horth : ∀ (x : P) (y : Q), F x.val y.val = 0)
    (hpos : ∀ x : P, x ≠ 0 → 0 < (F x.val x.val).re)
    (hneg : ∀ x : Q, x ≠ 0 → (F x.val x.val).re < 0)
    (p q : ℕ) (hp : Module.finrank ℂ P = p) (hq : Module.finrank ℂ Q = q) :
    ∃ e : V ≃ₗ[ℂ] ((Fin p → ℂ) × (Fin q → ℂ)), ∀ x y : V,
      F x y = (∑ i, (e x).1 i * star ((e y).1 i)) -
        ∑ j, (e x).2 j * star ((e y).2 j) := by
  let FP := ReferenceFamily.Complex.HermitianMatrixForm.restrictHermitianForm F P
  let FQ := -ReferenceFamily.Complex.HermitianMatrixForm.restrictHermitianForm F Q
  have hPsym (x y : P) : FP y x = star (FP x y) := hsym x.val y.val
  have hQsym (x y : Q) : FQ y x = star (FQ x y) := by
    change -F y.val x.val = star (-F x.val y.val)
    rw [hsym, star_neg]
  have hQpos (x : Q) (hx : x ≠ 0) : 0 < (FQ x x).re := by
    change 0 < (-F x.val x.val).re
    rw [Complex.neg_re]
    exact neg_pos.mpr (hneg x hx)
  obtain ⟨ep, hep⟩ := PositiveHermitianCoordinates.exists_positiveHermitian_coordinates FP hPsym hpos p hp
  obtain ⟨eq, heq⟩ := PositiveHermitianCoordinates.exists_positiveHermitian_coordinates FQ hQsym hQpos q hq
  let d := Submodule.prodEquivOfIsCompl P Q hPQ
  let e := d.symm.trans (ep.prodCongr eq)
  refine ⟨e, ?_⟩
  intro x y
  obtain ⟨⟨px, qx⟩, rfl⟩ := d.surjective x
  obtain ⟨⟨py, qy⟩, rfl⟩ := d.surjective y
  have her (a : P × Q) : e (d a) = (ep a.1, eq a.2) :=
    congrArg (ep.prodCongr eq) (d.symm_apply_apply a)
  rw [her, her]
  have hrev : F qx.val py.val = 0 := (hsym py.val qx.val).trans
    ((congrArg star (horth py qx)).trans (map_zero (starRingEnd ℂ)))
  have hsum : F (px.val + qx.val) (py.val + qy.val) = F px.val py.val + F qx.val qy.val := by
    simp only [map_add, LinearMap.add_apply, horth px qy, hrev, add_zero, zero_add]
  have heP : F px.val py.val = ∑ i, ep px i * star (ep py i) := hep px py
  have heQ : F qx.val qy.val = -(∑ j, eq qx j * star (eq qy j)) := neg_eq_iff_eq_neg.mp (heq qx qy)
  exact hsum.trans ((congrArg₂ (· + ·) heP heQ).trans (sub_eq_add_neg _ _).symm)

end

/-! Rescale the negative coordinate to the prescribed negative real
diagonal entry. The normalizer is an actual complex linear equivalence. -/

def threeSignedCoordinates (c : ℂ) (hc : c ≠ 0) :
    (Fin 3 → ℂ) ≃ₗ[ℂ] ((Fin 2 → ℂ) × (Fin 1 → ℂ)) where
  toFun x := (![x 0, x 1], ![c * x 2])
  invFun p := ![p.1 0, p.1 1, p.2 0 / c]
  left_inv x := by
    ext i
    fin_cases i <;> simp [hc]
  right_inv p := by
    apply Prod.ext
    · ext i
      fin_cases i <;> simp
    · ext i
      fin_cases i
      change c * (p.2 0 / c) = p.2 0
      field_simp
  map_add' x y := by
    apply Prod.ext
    · ext i
      fin_cases i <;> simp
    · ext i
      fin_cases i
      simp [mul_add]
  map_smul' a x := by
    apply Prod.ext
    · ext i
      fin_cases i <;> simp
    · ext i
      fin_cases i
      simp [mul_left_comm]

theorem complexHermitianMatrixForm_diagonal (β : ℂ) (x y : Fin 3 → ℂ) :
    ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm (Matrix.diagonal ![1, 1, β]) x y =
      x 0 * star (y 0) + x 1 * star (y 1) + β * x 2 * star (y 2) := by
  rw [ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm_apply]
  simp [Fin.sum_univ_succ, Matrix.diagonal]
  ring

theorem negativeReal_sqrt_factor (β : ℂ) (hreal : β.im = 0) (hneg : β.re < 0) :
    let c : ℂ := (Real.sqrt (-β.re) : ℂ)
    c ≠ 0 ∧ c * star c = -β := by
  have hp : 0 < Real.sqrt (-β.re) := Real.sqrt_pos.2 (neg_pos.mpr hneg)
  refine ⟨by exact_mod_cast hp.ne', ?_⟩
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im,
      Complex.ofReal_re, Complex.ofReal_im, neg_zero, mul_zero, sub_zero, Complex.neg_re]
    exact Real.mul_self_sqrt (neg_nonneg.mpr hneg.le)
  · simp [hreal]

theorem threeSignedCoordinates_form (β : ℂ) (c : ℂ) (hc : c ≠ 0)
    (hfactor : c * star c = -β) (x y : Fin 3 → ℂ) :
    (∑ i, (threeSignedCoordinates c hc x).1 i * star ((threeSignedCoordinates c hc y).1 i)) -
      ∑ j, (threeSignedCoordinates c hc x).2 j * star ((threeSignedCoordinates c hc y).2 j) =
        ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm (Matrix.diagonal ![1, 1, β]) x y := by
  rw [complexHermitianMatrixForm_diagonal]
  change (∑ i, (![x 0, x 1] : Fin 2 → ℂ) i * star ((![y 0, y 1] : Fin 2 → ℂ) i)) -
    (∑ j, (![c * x 2] : Fin 1 → ℂ) j * star ((![c * y 2] : Fin 1 → ℂ) j)) = _
  simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.sum_univ_zero, add_zero, star_mul]
  calc
    _ = x 0 * star (y 0) + x 1 * star (y 1) - (c * star c) * x 2 * star (y 2) := by ring
    _ = _ := by rw [hfactor]; ring

theorem exists_prescribedDiagonal_normalizer
    (F : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) →ₗ⋆[ℂ] ℂ)
    (e : (Fin 3 → ℂ) ≃ₗ[ℂ] ((Fin 2 → ℂ) × (Fin 1 → ℂ)))
    (he : ∀ x y, F x y = (∑ i, (e x).1 i * star ((e y).1 i)) -
      ∑ j, (e x).2 j * star ((e y).2 j))
    (β : ℂ) (hreal : β.im = 0) (hneg : β.re < 0) :
    ∃ n : (Fin 3 → ℂ) ≃ₗ[ℂ] (Fin 3 → ℂ), ∀ x y,
      F (n x) (n y) = ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm (Matrix.diagonal ![1, 1, β]) x y := by
  obtain ⟨hc, hfactor⟩ := negativeReal_sqrt_factor β hreal hneg
  let c : ℂ := (Real.sqrt (-β.re) : ℂ)
  let d := threeSignedCoordinates c hc
  let n := d.trans e.symm
  refine ⟨n, ?_⟩
  intro x y
  have hn (z : Fin 3 → ℂ) : e (n z) = d z := e.apply_symm_apply (d z)
  rw [he, hn, hn]
  exact threeSignedCoordinates_form β c hc hfactor x y

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.OrthogonalHermitianCoordinates
