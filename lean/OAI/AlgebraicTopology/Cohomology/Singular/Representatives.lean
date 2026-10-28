import OAI.AlgebraicTopology.Cohomology.Singular.Basic
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Representatives -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.Representatives

noncomputable section

/-!
# Cocycles, coboundaries, and representatives of singular cohomology

The quotient descriptions here are the explicit module quotients already identified
with categorical homology by mathlib's `ShortComplex.moduleCatHomologyIso`. In
particular, no independently chosen cohomology theory or comparison axiom is used.
The final declarations specialize this description to `singularCochains`.
-/

open _root_.CategoryTheory

variable {R : Type} [Ring R]

/-- The kernel of the outgoing differential in a cochain complex. -/
abbrev cochainCocycles (K : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) :
    Submodule R (K.X n) :=
  LinearMap.ker (K.sc n).g.hom

/-- The incoming differential, with its codomain restricted to cocycles. -/
abbrev cochainBoundaryMap (K : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) :
    (K.sc n).X₁ →ₗ[R] cochainCocycles K n :=
  (K.sc n).moduleCatToCycles

/-- Coboundaries as a submodule of cocycles. -/
abbrev cochainBoundaries (K : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) :
    Submodule R (cochainCocycles K n) :=
  LinearMap.range (cochainBoundaryMap K n)

/-- Mathlib's categorical cohomology is the quotient of cocycles by coboundaries. -/
def cohomologyQuotientIso (K : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) :
    K.homology n ≅ ModuleCat.of R (cochainCocycles K n ⧸ cochainBoundaries K n) :=
  (K.sc n).moduleCatHomologyIso

/-- The cohomology class of a cocycle. -/
def cochainClass (K : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) :
    cochainCocycles K n →ₗ[R] K.homology n :=
  (cohomologyQuotientIso K n).toLinearEquiv.symm.toLinearMap.comp
    (cochainBoundaries K n).mkQ

@[simp]
theorem mem_cochainCocycles_iff (K : CochainComplex (ModuleCat.{0} R) ℕ)
    (n : ℕ) (x : K.X n) :
    x ∈ cochainCocycles K n ↔ (K.d n (n + 1)) x = 0 := by
  change (K.d n ((ComplexShape.up ℕ).next n)) x = 0 ↔ _
  rw [(ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl)]

/-- The class map just defined is the canonical categorical homology projection. -/
theorem cochainClass_eq_homologyπ (K : CochainComplex (ModuleCat.{0} R) ℕ)
    (n : ℕ) (x : cochainCocycles K n) :
    cochainClass K n x =
      (K.homologyπ n) ((K.sc n).moduleCatCyclesIso.inv x) := by
  change (K.sc n).moduleCatHomologyIso.inv ((K.sc n).moduleCatLeftHomologyData.π x) =
    (K.sc n).homologyπ ((K.sc n).moduleCatCyclesIso.inv x)
  exact (ConcreteCategory.congr_hom ((K.sc n).moduleCatCyclesIso_inv_π) x).symm

/-- Every categorical cohomology class has a cocycle representative. -/
theorem cochainClass_surjective (K : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) :
    Function.Surjective (cochainClass K n) :=
  (cohomologyQuotientIso K n).toLinearEquiv.symm.surjective.comp
    (cochainBoundaries K n).mkQ_surjective

/-- Two cocycles have the same class exactly when their difference is a coboundary. -/
theorem cochainClass_eq_iff (K : CochainComplex (ModuleCat.{0} R) ℕ)
    (n : ℕ) (x y : cochainCocycles K n) :
    cochainClass K n x = cochainClass K n y ↔ x - y ∈ cochainBoundaries K n := by
  change (cohomologyQuotientIso K n).toLinearEquiv.symm ((cochainBoundaries K n).mkQ x) =
      (cohomologyQuotientIso K n).toLinearEquiv.symm ((cochainBoundaries K n).mkQ y) ↔ _
  rw [(cohomologyQuotientIso K n).toLinearEquiv.symm.injective.eq_iff]
  exact Submodule.Quotient.eq _

/-- Equality of classes expressed using an actual primitive for the difference. -/
theorem cochainClass_eq_iff_exists (K : CochainComplex (ModuleCat.{0} R) ℕ)
    (n : ℕ) (x y : cochainCocycles K n) :
    cochainClass K n x = cochainClass K n y ↔
      ∃ z : (K.sc n).X₁, (K.sc n).f z = (x : K.X n) - (y : K.X n) := by
  rw [cochainClass_eq_iff]
  change (∃ z, cochainBoundaryMap K n z = x - y) ↔ _
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, congrArg Subtype.val hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, Subtype.ext hz⟩

/-- In degree `n + 1`, an equal pair of classes differs by the differential
of an actual degree-`n` cochain. -/
theorem cochainClass_eq_iff_exists_succ (K : CochainComplex (ModuleCat.{0} R) ℕ)
    (n : ℕ) (x y : cochainCocycles K (n + 1)) :
    cochainClass K (n + 1) x = cochainClass K (n + 1) y ↔
      ∃ z : K.X n, (K.d n (n + 1)) z =
        (x : K.X (n + 1)) - (y : K.X (n + 1)) := by
  rw [cochainClass_eq_iff_exists]
  change (∃ z : K.X ((ComplexShape.up ℕ).prev (n + 1)),
    (K.d ((ComplexShape.up ℕ).prev (n + 1)) (n + 1)) z =
      (x : K.X (n + 1)) - (y : K.X (n + 1))) ↔ _
  rw [(ComplexShape.up ℕ).prev_eq'
    (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl)]

@[simp]
theorem cochainClass_eq_zero_iff (K : CochainComplex (ModuleCat.{0} R) ℕ)
    (n : ℕ) (x : cochainCocycles K n) :
    cochainClass K n x = 0 ↔ x ∈ cochainBoundaries K n := by
  simpa using cochainClass_eq_iff K n x 0

/-- Cocycles in the genuine singular cochain complex. -/
abbrev singularCocycles (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ) :=
  cochainCocycles (Basic.singularCochains M X) n

/-- Singular coboundaries, viewed as a submodule of singular cocycles. -/
abbrev singularBoundaries (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ) :=
  cochainBoundaries (Basic.singularCochains M X) n

/-- The explicit cocycle/coboundary quotient of genuine singular cohomology. -/
abbrev singularCohomologyQuotientIso (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ) :
    Basic.singularCohomology M X n ≅
      ModuleCat.of R (singularCocycles M X n ⧸ singularBoundaries M X n) :=
  cohomologyQuotientIso (Basic.singularCochains M X) n

/-- The singular cohomology class of a singular cocycle. -/
abbrev singularClass (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ) :
    singularCocycles M X n →ₗ[R] Basic.singularCohomology M X n :=
  cochainClass (Basic.singularCochains M X) n

/-- Every genuine singular cohomology class has a singular cocycle representative. -/
theorem singularClass_surjective (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ) :
    Function.Surjective (singularClass M X n) :=
  cochainClass_surjective (Basic.singularCochains M X) n

/-- The usual cocycle-modulo-coboundary equality criterion for singular classes. -/
theorem singularClass_eq_iff (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ)
    (x y : singularCocycles M X n) :
    singularClass M X n x = singularClass M X n y ↔ x - y ∈ singularBoundaries M X n :=
  cochainClass_eq_iff (Basic.singularCochains M X) n x y

/-- Equality of positive-degree singular classes is precisely the existence
of a singular cochain whose coboundary is their difference. -/
theorem singularClass_eq_iff_exists_succ (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (n : ℕ) (x y : singularCocycles M X (n + 1)) :
    singularClass M X (n + 1) x = singularClass M X (n + 1) y ↔
      ∃ z : (Basic.singularCochains M X).X n,
        ((Basic.singularCochains M X).d n (n + 1)) z =
          (x : (Basic.singularCochains M X).X (n + 1)) -
            (y : (Basic.singularCochains M X).X (n + 1)) :=
  cochainClass_eq_iff_exists_succ (Basic.singularCochains M X) n x y

@[simp]
theorem singularClass_eq_zero_iff (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ)
    (x : singularCocycles M X n) :
    singularClass M X n x = 0 ↔ x ∈ singularBoundaries M X n :=
  cochainClass_eq_zero_iff (Basic.singularCochains M X) n x

end

end OAI.AlgebraicTopology.Cohomology.Singular.Representatives
