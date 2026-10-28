import OAI.Algorithms.SubexponentialSAT.LeanCompat

namespace OAI.Algorithms

/-!
# The finite extension and its defining polynomial

For each prime `p` and positive `h`, the field is constructed as mathlib's
`GaloisField p h`. Its size and extension degree are proved, not assumed.
A primitive element provides a monic irreducible polynomial of degree `h`,
and its polynomial quotient is identified with the same field.

The chosen primitive element and finite enumeration are noncomputable choices
of fixed finite objects. This module proves their mathematical existence and
properties; it does not claim an executable field-construction complexity bound.
-/

noncomputable section
namespace SubexponentialSAT.FiniteField

open Polynomial

/-- The actual finite extension used for interpolation nodes. -/
abbrev E (p h : ℕ) [Fact p.Prime] := GaloisField p h

instance fieldFintype (p h : ℕ) [Fact p.Prime] : Fintype (E p h) :=
  Fintype.ofFinite _

variable (p h : ℕ) [Fact p.Prime]

theorem extension_finrank (hh : h ≠ 0) :
    Module.finrank (ZMod p) (E p h) = h :=
  GaloisField.finrank p hh

theorem extension_natCard (hh : h ≠ 0) : Nat.card (E p h) = p ^ h :=
  GaloisField.card p h hh

theorem extension_card (hh : h ≠ 0) : Fintype.card (E p h) = p ^ h := by
  rw [← Nat.card_eq_fintype_card]
  exact extension_natCard p h hh

/-- All nonzero elements, indexed by exactly `p^h - 1` positions. -/
def nodeEquiv (hh : h ≠ 0) : Fin (p ^ h - 1) ≃ {x : E p h // x ≠ 0} := by
  classical
  apply (Fintype.equivFinOfCardEq _).symm
  rw [Fintype.card_subtype_compl]
  simp [extension_card p h hh]

def node (hh : h ≠ 0) (t : Fin (p ^ h - 1)) : E p h :=
  (nodeEquiv p h hh t).val

@[simp] theorem node_ne_zero (hh : h ≠ 0) (t : Fin (p ^ h - 1)) :
    node p h hh t ≠ 0 := (nodeEquiv p h hh t).property

theorem node_injective (hh : h ≠ 0) : Function.Injective (node p h hh) := by
  intro s t heq
  exact (nodeEquiv p h hh).injective (Subtype.ext heq)

theorem node_complete (hh : h ≠ 0) {x : E p h} (hx : x ≠ 0) :
    ∃ t, node p h hh t = x := by
  obtain ⟨t, ht⟩ := (nodeEquiv p h hh).surjective ⟨x, hx⟩
  exact ⟨t, congrArg Subtype.val ht⟩

/-- A primitive element of the constructed field, chosen once for `p,h`. -/
def primitiveElement : E p h :=
  (Field.exists_primitive_element_of_finite_top (ZMod p) (E p h)).choose

theorem primitiveElement_adjoin :
    IntermediateField.adjoin (ZMod p) ({primitiveElement p h} : Set (E p h)) = ⊤ :=
  (Field.exists_primitive_element_of_finite_top (ZMod p) (E p h)).choose_spec

theorem primitiveElement_integral : IsIntegral (ZMod p) (primitiveElement p h) :=
  IsIntegral.of_finite (ZMod p) _

/-- The monic irreducible polynomial defining the same extension. -/
def definingPolynomial : (ZMod p)[X] :=
  minpoly (ZMod p) (primitiveElement p h)

theorem definingPolynomial_monic : (definingPolynomial p h).Monic :=
  minpoly.monic (primitiveElement_integral p h)

theorem definingPolynomial_irreducible : Irreducible (definingPolynomial p h) :=
  minpoly.irreducible (primitiveElement_integral p h)

theorem definingPolynomial_natDegree (hh : h ≠ 0) :
    (definingPolynomial p h).natDegree = h := by
  change (minpoly (ZMod p) (primitiveElement p h)).natDegree = h
  rw [(Field.primitive_element_iff_minpoly_natDegree_eq (ZMod p)
    (primitiveElement p h)).mp (primitiveElement_adjoin p h)]
  exact extension_finrank p h hh

theorem definingPolynomial_aeval :
    Polynomial.aeval (primitiveElement p h) (definingPolynomial p h) = 0 :=
  minpoly.aeval (ZMod p) (primitiveElement p h)

/-- In particular the needed defining polynomial exists for every positive
extension degree; it is not an assumption about the construction. -/
theorem exists_monic_irreducible (hh : h ≠ 0) :
    ∃ f : (ZMod p)[X], f.Monic ∧ Irreducible f ∧ f.natDegree = h :=
  ⟨definingPolynomial p h, definingPolynomial_monic p h,
    definingPolynomial_irreducible p h, definingPolynomial_natDegree p h hh⟩

/-- Identify the polynomial quotient with the very same field used by the
interpolation layout, rather than an unrelated field of the same cardinality. -/
def quotientEquiv : AdjoinRoot (definingPolynomial p h) ≃ₐ[ZMod p] E p h :=
  (IntermediateField.adjoinRootEquivAdjoin (ZMod p) (primitiveElement_integral p h)).trans
    ((IntermediateField.equivOfEq (primitiveElement_adjoin p h)).trans
      IntermediateField.topEquiv)

/-- The identical equivalence written in the raw polynomial-quotient form used
by `SubexponentialSAT.LiftRing.Extension`, without importing that module. -/
def polynomialQuotientEquiv :
    ((ZMod p)[X] ⧸ Ideal.span {definingPolynomial p h}) ≃ₐ[ZMod p] E p h :=
  quotientEquiv p h

theorem polynomialQuotientEquiv_algebraMap (a : ZMod p) :
    polynomialQuotientEquiv p h
        (algebraMap (ZMod p) ((ZMod p)[X] ⧸ Ideal.span {definingPolynomial p h}) a) =
      algebraMap (ZMod p) (E p h) a :=
  (polynomialQuotientEquiv p h).commutes a

end SubexponentialSAT.FiniteField

end

end OAI.Algorithms
