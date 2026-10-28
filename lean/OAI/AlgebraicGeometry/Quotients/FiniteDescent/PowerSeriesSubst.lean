import Mathlib.RingTheory.MvPowerSeries.Equiv

/-! # Power Series Subst -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.PowerSeriesSubst.Construction.PowerSeriesShear

noncomputable section

/-! Invertible linear changes of coordinates for finite-variable power series. -/

open MvPowerSeries

variable {R : Type*} [CommRing R] {n : ℕ}

def coordinates (a : Fin n → R) : Fin (n + 1) → MvPowerSeries (Fin (n + 1)) R :=
  Fin.cases (X 0) (fun i => X i.succ + a i • X 0)

theorem coordinates_zero (a : Fin n → R) : coordinates a 0 = X 0 := rfl

theorem coordinates_succ (a : Fin n → R) (i : Fin n) :
    coordinates a i.succ = X i.succ + a i • X 0 := rfl

theorem hasSubst (a : Fin n → R) : HasSubst (coordinates a) := by
  apply hasSubst_of_constantCoeff_zero
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [coordinates_zero]
  · simp [coordinates_succ]

theorem subst_coordinates (a b : Fin n → R) (i : Fin (n + 1)) :
    subst (coordinates b) (coordinates a i) = coordinates (a + b) i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [coordinates_zero, subst_X (hasSubst b)]
  · simp only [coordinates_succ, subst_add (hasSubst b), subst_X (hasSubst b),
      subst_smul (hasSubst b), coordinates_zero, Pi.add_apply, add_smul]
    abel

theorem subst_neg_subst (a : Fin n → R) (f : MvPowerSeries (Fin (n + 1)) R) :
    subst (coordinates (-a)) (subst (coordinates a) f) = f := by
  rw [subst_comp_subst_apply (hasSubst a) (hasSubst (-a))]
  have he : (fun i => subst (coordinates (-a)) (coordinates a i)) = X := by
    funext i
    rw [subst_coordinates]
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp [coordinates_succ]
  rw [he, subst_self]
  rfl

def equiv (a : Fin n → R) :
    MvPowerSeries (Fin (n + 1)) R ≃ₐ[R] MvPowerSeries (Fin (n + 1)) R where
  __ := substAlgHom (R := R) (hasSubst a)
  invFun := subst (coordinates (-a))
  left_inv f := by
    change subst (coordinates (-a)) (substAlgHom (hasSubst a) f) = f
    rw [substAlgHom_apply]
    exact subst_neg_subst a f
  right_inv f := by simpa using subst_neg_subst (-a) f

theorem equiv_apply (a : Fin n → R) (f : MvPowerSeries (Fin (n + 1)) R) :
    equiv a f = subst (coordinates a) f := substAlgHom_apply (hasSubst a) f

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.PowerSeriesSubst.Construction.PowerSeriesShear
