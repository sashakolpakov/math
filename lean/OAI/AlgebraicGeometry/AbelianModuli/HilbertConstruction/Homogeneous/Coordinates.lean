import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Basis.Defs

/-! # Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.Coordinates

noncomputable section

/-!
Canonical monomial coordinates for each homogeneous polynomial degree.
They identify the finite free degree module with a coordinate module used by
the constructed Grassmannian parameter schemes.
-/

universe u v

abbrev HomogeneousMonomials (σ : Type v) (d : ℕ) := {a : σ →₀ ℕ // a.degree = d}

instance homogeneousMonomials_decidableEq (σ : Type v) (d : ℕ) :
    DecidableEq (HomogeneousMonomials σ d) := Classical.decEq _

instance homogeneousMonomials_fintype (σ : Type v) [Finite σ] (d : ℕ) :
    Fintype (HomogeneousMonomials σ d) := (Finsupp.finite_of_degree_eq d).fintype

instance homogeneousMonomials_nonempty (σ : Type v) [Nonempty σ] (d : ℕ) :
    Nonempty (HomogeneousMonomials σ d) := by
  classical
  exact ⟨⟨Finsupp.single (Classical.choice (inferInstance : Nonempty σ)) d, by simp⟩⟩

variable (R : Type u) [CommRing R] (σ : Type v) [Finite σ] (d : ℕ)

def homogeneousSupportEquiv :
    MvPolynomial.homogeneousSubmodule σ R d ≃ₗ[R]
      MvPolynomial.restrictSupport R {a : σ →₀ ℕ | a.degree = d} where
  toFun p := ⟨p.val, by
    change p.val ∈ AddMonoidAlgebra.supported R R {a : σ →₀ ℕ | a.degree = d}
    rw [← MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
    exact p.property⟩
  invFun p := ⟨p.val, by
    rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
    exact p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def homogeneousMonomialBasis : Module.Basis (HomogeneousMonomials σ d) R
    (MvPolynomial.homogeneousSubmodule σ R d) :=
  (MvPolynomial.basisRestrictSupport R {a : σ →₀ ℕ | a.degree = d}).map
    (homogeneousSupportEquiv R σ d).symm

def homogeneousCoordinates : MvPolynomial.homogeneousSubmodule σ R d ≃ₗ[R]
    (HomogeneousMonomials σ d → R) :=
  (homogeneousMonomialBasis R σ d).equivFun

theorem homogeneousCoordinates_apply (p : MvPolynomial.homogeneousSubmodule σ R d)
    (a : HomogeneousMonomials σ d) :
    homogeneousCoordinates R σ d p a = AddMonoidAlgebra.coeff (p.val) (a.val) := by
  rw [homogeneousCoordinates, Module.Basis.equivFun_apply]
  rfl

theorem homogeneousCoordinates_coefficientMap {A : Type*} [CommRing A] (φ : R →+* A)
    (p : MvPolynomial.homogeneousSubmodule σ R d) :
    homogeneousCoordinates A σ d ⟨MvPolynomial.map φ p.val, p.property.map φ⟩ =
      φ ∘ homogeneousCoordinates R σ d p := by
  funext a
  rw [Function.comp_apply, homogeneousCoordinates_apply, homogeneousCoordinates_apply]
  exact MvPolynomial.coeff_map φ p.val a.val

theorem homogeneousCoordinates_monomial (a : HomogeneousMonomials σ d) (r : R) :
    homogeneousCoordinates R σ d ⟨MvPolynomial.monomial a.val r,
      MvPolynomial.isHomogeneous_monomial r a.property⟩ = Pi.single a r := by
  classical
  funext b
  rw [homogeneousCoordinates_apply]
  simp only [MvPolynomial.coeff_monomial, Pi.single_apply, Subtype.ext_iff, eq_comm]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.Coordinates
