import Mathlib.AlgebraicGeometry.Properties

/-! # Cycle Supports -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.CycleSupports

noncomputable section

/-!
# Generic points and codimension-indexed algebraic cycle supports

This file identifies codimension-indexed scheme points with irreducible closed
supports. Codimension is the coheight in the specialization order, equivalently
in the inclusion order on irreducible closed sets. No cycle class map is assumed.
-/

open _root_.AlgebraicGeometry _root_.TopologicalSpace _root_.Order

universe u

/-- A generic point of an irreducible codimension-`p` algebraic cycle support. -/
def CyclePoint (X : Scheme.{u}) (p : ℕ) : Type u :=
  {x : X // Order.coheight x = p}

/-- An irreducible closed algebraic support of codimension `p`. -/
def IrreducibleCycleSupport (X : Scheme.{u}) (p : ℕ) : Type u :=
  {Z : IrreducibleCloseds X // Order.coheight Z = p}

/-- Scheme sobriety identifies irreducible closed sets with their generic points,
and its order isomorphism preserves codimension. -/
def irreducibleCycleSupportEquivCyclePoint (X : Scheme.{u}) (p : ℕ) :
    IrreducibleCycleSupport X p ≃ CyclePoint X p where
  toFun Z := ⟨irreducibleSetEquivPoints Z.1, by
    rw [Order.coheight_orderIso]
    exact Z.2⟩
  invFun x := ⟨irreducibleSetEquivPoints.symm x.1, by
    rw [Order.coheight_orderIso]
    exact x.2⟩
  left_inv Z := by
    apply Subtype.ext
    exact irreducibleSetEquivPoints.symm_apply_apply Z.1
  right_inv x := by
    apply Subtype.ext
    exact irreducibleSetEquivPoints.apply_symm_apply x.1

/-- The irreducible support corresponding to a cycle point is its closure. -/
theorem cyclePoint_support_coe (X : Scheme.{u}) (p : ℕ) (x : CyclePoint X p) :
    (((irreducibleCycleSupportEquivCyclePoint X p).symm x).1 : Set X) =
      closure ({x.1} : Set X) := rfl

/-- The point indexing a support is indeed its generic point. -/
theorem cycleSupport_isGenericPoint (X : Scheme.{u}) (p : ℕ)
    (Z : IrreducibleCycleSupport X p) :
    IsGenericPoint ((irreducibleCycleSupportEquivCyclePoint X p Z).1)
      (Z.1 : Set X) :=
  Z.1.2.isGenericPoint_genericPoint Z.1.3

/-- Codimension can equivalently be read off from the dimension of the local ring. -/
theorem cyclePoint_stalk_dimension (X : Scheme.{u}) (p : ℕ) (x : CyclePoint X p) :
    ringKrullDim (X.presheaf.stalk x.1) = (p : WithBot ℕ∞) := by
  rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight, x.2]
  rfl

/-- On an affine scheme, the indexing codimension is the height of its prime ideal. -/
theorem cyclePoint_affine_prime_height (R : CommRingCat.{u}) (p : ℕ)
    (x : CyclePoint (Spec R) p) : x.1.asIdeal.height = p := by
  rw [AlgebraicGeometry.idealHeight_eq_coheight]
  exact x.2

end

end OAI.AlgebraicGeometry.Foundations.Scheme.CycleSupports
