import Mathlib

/-! # Cotangent Bundle -/

namespace OAI.Geometry.ComplexBall.CotangentBundle

/-!
# CotangentBundle: determinant and cotangent identities in the committed bundle calculus

The definitions below reproduce Statements/CotangentBundle.lean in a unique namespace;
no statement stub is imported or used. All hypotheses of that specification
are retained, including the explicitly named decomposition input `h_PrescribedSigns`.

The coordinate existence proposition in Statements/PrescribedSigns.lean is unnecessary
for this abstract implication: the target already assumes the decomposition
as an equality of bundle classes. That coordinate specification does not
provide a map from its holomorphic submodule families to BundleCalculus.
Realizing this calculus geometrically, and deriving `h_PrescribedSigns` through such a
map, remain the previously documented modeling interface; they are not
asserted or hidden in any new hypothesis here. No additional assumption is
needed for the committed target. The rank-three hypothesis gives rank two
for the quotient, as in the manuscript's displayed summands.

As in the specification, fixed nonzero trivializations identify constant
trivial-representation lines with class 1. The cotangent is the dual of
the projective tangent model Hom(L,Q). The half-determinant clause constructs
a square root, without identifying an independently chosen metaplectic lift.
-/

universe u v

/-- Equivariant holomorphic bundle-class calculus from the specification. -/
structure BundleCalculus
    (B : Type u) (A : Type v)
    [CommSemiring B] [CommGroup A] where
  line : A →* B
  rank : B →+* ℕ
  dual : B →+* B
  det : B → A
  shortExact : B → B → B → Prop

  rank_line : ∀ a, rank (line a) = 1
  rank_dual : ∀ X, rank (dual X) = rank X
  dual_involutive : ∀ X, dual (dual X) = X

  det_line : ∀ a, det (line a) = a
  det_sum : ∀ X Y, det (X + Y) = det X * det Y
  det_tensor : ∀ X Y,
    det (X * Y) = det X ^ rank Y * det Y ^ rank X
  det_dual : ∀ X, det (dual X) = (det X)⁻¹

  rank_exact : ∀ X Y Z, shortExact X Y Z →
    rank Y = rank X + rank Z
  det_exact : ∀ X Y Z, shortExact X Y Z →
    det Y = det X * det Z

variable {B : Type u} {A : Type v}
  [CommSemiring B] [CommGroup A]

/-- Cotangent class in the projective tangent model, copied from the target. -/
def projectiveCotangent
    (C : BundleCalculus B A) (L : A) (Q : B) : B :=
  C.dual (C.dual (C.line L) * Q)

/-- The full committed CotangentBundle conclusion, conditional on its named inputs. -/
theorem determinant_and_cotangent_identities
    (C : BundleCalculus B A)
    (n : ℕ) (L : A) (Vμ Q P K ℱ : B)
    (h_rankV : C.rank Vμ = 3)
    (h_rankP : C.rank P = n)
    (h_quotient : C.shortExact (C.line L) Vμ Q)
    (h_specialUnitary : C.det Vμ = 1)
    (h_multiplicity : C.det P = 1)
    (h_compactPlaces : C.det K = 1)
    (h_PrescribedSigns :
      ℱ = C.line L * P + C.dual Q * C.dual P + K) :
    C.det ℱ = L ^ (2 * n) ∧
    (∃ H : A, H = L ^ n ∧ H ^ 2 = C.det ℱ) ∧
    projectiveCotangent C L Q = C.line L * C.dual Q := by
  have h_rankQ : C.rank Q = 2 := by
    have hexact := C.rank_exact (C.line L) Vμ Q h_quotient
    rw [h_rankV, C.rank_line] at hexact
    omega
  have hdetQ : C.det Q = L⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    have hexact := C.det_exact (C.line L) Vμ Q h_quotient
    rw [C.det_line, h_specialUnitary] at hexact
    exact hexact.symm
  have hdet : C.det ℱ = L ^ (2 * n) := by
    rw [h_PrescribedSigns, C.det_sum, C.det_sum, C.det_tensor, C.det_tensor]
    simp only [C.det_line, C.det_dual, C.rank_dual, h_rankP, h_rankQ,
      h_multiplicity, h_compactPlaces, hdetQ, inv_inv, inv_one,
      one_pow, mul_one]
    rw [← pow_add, ← two_mul]
  refine ⟨hdet, ⟨L ^ n, rfl, ?_⟩, ?_⟩
  · rw [hdet, ← pow_mul, Nat.mul_comm n 2]
  · unfold projectiveCotangent
    rw [map_mul, C.dual_involutive]

end OAI.Geometry.ComplexBall.CotangentBundle
