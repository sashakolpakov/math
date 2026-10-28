import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Coprime.Basic

/-! # Scalar Quotient Mk -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.ScalarQuotientMk

noncomputable section

/-! An isogeny of modules whose scalar degree is coprime to the modulus
induces an actual linear equivalence on the quotient modules. The maps
and inverse are constructed from a Bezout identity. -/

variable {R M P : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup P] [Module R P]

def scalarMultiples (n : R) : Submodule R M :=
  LinearMap.range (n • (LinearMap.id : M →ₗ[R] M))

abbrev ScalarQuotient (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    (n : R) := M ⧸ scalarMultiples (M := M) n

theorem scalarQuotient_killed (n : R) (x : ScalarQuotientMk.ScalarQuotient R M n) : n • x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    change (scalarMultiples (M := M) n).mkQ (n • x) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨x, rfl⟩

def scalarQuotientMap (n : R) (f : M →ₗ[R] P) :
    ScalarQuotientMk.ScalarQuotient R M n →ₗ[R] ScalarQuotientMk.ScalarQuotient R P n :=
  (scalarMultiples n).mapQ (scalarMultiples n) f (by
    rintro _ ⟨x, rfl⟩
    exact ⟨f x, (f.map_smul n x).symm⟩)

@[simp] theorem scalarQuotientMap_mk (n : R) (f : M →ₗ[R] P) (x : M) :
    scalarQuotientMap n f (Submodule.Quotient.mk x) = Submodule.Quotient.mk (f x) := rfl

theorem scalarQuotientMap_composite (n c : R) (f : M →ₗ[R] P) (g : P →ₗ[R] M)
    (h : ∀ x, g (f x) = c • x) (x : ScalarQuotientMk.ScalarQuotient R M n) :
    scalarQuotientMap n g (scalarQuotientMap n f x) = c • x := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    change (scalarMultiples (M := M) n).mkQ (g (f x)) =
      c • (scalarMultiples (M := M) n).mkQ x
    rw [h, map_smul]

theorem bezout_smul_identity (n c a b : R) (h : a * c + b * n = 1)
    (x : M) (hx : n • x = 0) : a • (c • x) = x := by
  have he := congrArg (fun r : R => r • x) h
  simpa only [add_smul, mul_smul, hx, smul_zero, add_zero, one_smul] using he

/-- A pair of maps with both composites equal to a scalar gives an
equivalence modulo every modulus coprime to that scalar. -/
def scalarQuotientEquiv (n c : R) (hc : IsCoprime c n)
    (f : M →ₗ[R] P) (g : P →ₗ[R] M)
    (hgf : ∀ x, g (f x) = c • x) (hfg : ∀ x, f (g x) = c • x) :
    ScalarQuotientMk.ScalarQuotient R M n ≃ₗ[R] ScalarQuotientMk.ScalarQuotient R P n := by
  let a := hc.choose
  let b := hc.choose_spec.choose
  have hab : a * c + b * n = 1 := hc.choose_spec.choose_spec
  exact
    { scalarQuotientMap n f with
      invFun := fun y => a • scalarQuotientMap n g y
      left_inv := fun x => by
        change a • scalarQuotientMap n g (scalarQuotientMap n f x) = x
        rw [scalarQuotientMap_composite n c f g hgf]
        exact bezout_smul_identity n c a b hab x (scalarQuotient_killed n x)
      right_inv := fun y => by
        change scalarQuotientMap n f (a • scalarQuotientMap n g y) = y
        rw [map_smul, scalarQuotientMap_composite n c g f hfg]
        exact bezout_smul_identity n c a b hab y (scalarQuotient_killed n y) }

def scalarQuotientCongr (e : M ≃ₗ[R] P) (n : R) :
    ScalarQuotientMk.ScalarQuotient R M n ≃ₗ[R] ScalarQuotientMk.ScalarQuotient R P n :=
  scalarQuotientEquiv n 1 isCoprime_one_left e.toLinearMap e.symm.toLinearMap
    (fun x => (e.symm_apply_apply x).trans (one_smul R x).symm)
    (fun x => (e.apply_symm_apply x).trans (one_smul R x).symm)

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.ScalarQuotientMk
