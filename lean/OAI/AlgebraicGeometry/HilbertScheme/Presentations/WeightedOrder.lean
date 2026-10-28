import OAI.AlgebraicGeometry.HilbertScheme.Presentations.GroebnerGenerators
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.MonomialBasis
import Mathlib.Data.Finsupp.MonomialOrder.DegLex

/-! # Weighted Order -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.WeightedOrder.GradedHilbert

noncomputable section

/-!
Monomial orders with an additive weight compared first. Comparing total
degree and then the total exponent away from one chosen variable gives
an order that detects divisibility by that variable in homogeneous forms.
-/

open _root_.MvPolynomial
open scoped MonomialOrder

variable {n : ℕ}

def WeightedExponent (_m : MonomialOrder (Fin (n + 1)))
    (_w : (Fin (n + 1) →₀ ℕ) →+ ℕ) := Fin (n + 1) →₀ ℕ

def unweight (m : MonomialOrder (Fin (n + 1)))
    (w : (Fin (n + 1) →₀ ℕ) →+ ℕ) : WeightedExponent m w ≃ (Fin (n + 1) →₀ ℕ) :=
  Equiv.refl _

instance weightedAddCommMonoid (m : MonomialOrder (Fin (n + 1)))
    (w : (Fin (n + 1) →₀ ℕ) →+ ℕ) : AddCommMonoid (WeightedExponent m w) :=
  (unweight m w).addCommMonoid

def weightKey (m : MonomialOrder (Fin (n + 1)))
    (w : (Fin (n + 1) →₀ ℕ) →+ ℕ) (a : WeightedExponent m w) : ℕ ×ₗ m.syn :=
  toLex (w (unweight m w a), m.toSyn (unweight m w a))

theorem weightKey_injective (m : MonomialOrder (Fin (n + 1)))
    (w : (Fin (n + 1) →₀ ℕ) →+ ℕ) : Function.Injective (weightKey m w) := by
  intro a b h
  apply (unweight m w).injective
  apply m.toSyn.injective
  exact congrArg Prod.snd (toLex.injective h)

instance weightedLinearOrder (m : MonomialOrder (Fin (n + 1)))
    (w : (Fin (n + 1) →₀ ℕ) →+ ℕ) : LinearOrder (WeightedExponent m w) :=
  LinearOrder.lift' (weightKey m w) (weightKey_injective m w)

theorem weighted_le_iff (m : MonomialOrder (Fin (n + 1)))
    (w : (Fin (n + 1) →₀ ℕ) →+ ℕ) (a b : WeightedExponent m w) :
    a ≤ b ↔ w (unweight m w a) < w (unweight m w b) ∨
      w (unweight m w a) = w (unweight m w b) ∧
        m.toSyn (unweight m w a) ≤ m.toSyn (unweight m w b) :=
  Prod.Lex.toLex_le_toLex

instance weightedIsOrderedAddMonoid (m : MonomialOrder (Fin (n + 1)))
    (w : (Fin (n + 1) →₀ ℕ) →+ ℕ) : IsOrderedAddMonoid (WeightedExponent m w) where
  add_le_add_left a b h c := by
    rw [weighted_le_iff] at h ⊢
    change w (unweight m w a + unweight m w c) < w (unweight m w b + unweight m w c) ∨
      w (unweight m w a + unweight m w c) = w (unweight m w b + unweight m w c) ∧
        m.toSyn (unweight m w a + unweight m w c) ≤
          m.toSyn (unweight m w b + unweight m w c)
    simpa only [map_add, add_lt_add_iff_right, add_left_inj, add_le_add_iff_right] using h

instance weightedWellFoundedLT (m : MonomialOrder (Fin (n + 1)))
    (w : (Fin (n + 1) →₀ ℕ) →+ ℕ) : WellFoundedLT (WeightedExponent m w) :=
  InvImage.wf (fun a => (w (unweight m w a), m.toSyn (unweight m w a)))
    (WellFounded.prod_lex wellFounded_lt wellFounded_lt)

theorem exponent_weight_monotone (w : (Fin (n + 1) →₀ ℕ) →+ ℕ) : Monotone w := by
  intro a b hab
  obtain ⟨c, rfl⟩ := le_iff_exists_add.mp hab
  rw [map_add]
  exact Nat.le_add_right _ _

def prependWeight (m : MonomialOrder (Fin (n + 1)))
    (w : (Fin (n + 1) →₀ ℕ) →+ ℕ) : MonomialOrder (Fin (n + 1)) where
  syn := WeightedExponent m w
  toSyn := { toEquiv := (unweight m w).symm, map_add' := fun _ _ => rfl }
  toSyn_monotone a b hab := by
    apply Prod.Lex.toLex_le_toLex'.mpr
    exact ⟨exponent_weight_monotone w hab, fun _ => m.toSyn_monotone hab⟩

theorem prependWeight_le_iff (m : MonomialOrder (Fin (n + 1)))
    (w : (Fin (n + 1) →₀ ℕ) →+ ℕ) (a b : Fin (n + 1) →₀ ℕ) :
    a ≼[prependWeight m w] b ↔ w a < w b ∨ w a = w b ∧ a ≼[m] b :=
  weighted_le_iff m w _ _

def otherWeight (i : Fin (n + 1)) : (Fin (n + 1) →₀ ℕ) →+ ℕ where
  toFun a := ∑ j ∈ Finset.univ.erase i, a j
  map_zero' := by simp
  map_add' a b := by simp [Finset.sum_add_distrib]

theorem otherWeight_add (i : Fin (n + 1)) (a : Fin (n + 1) →₀ ℕ) :
    otherWeight i a + a i = a.degree := by
  change (∑ j ∈ Finset.univ.erase i, a j) + a i = a.degree
  rw [Finset.sum_erase_add _ _ (Finset.mem_univ i), Finsupp.degree_eq_sum]

def variableLastOrder (i : Fin (n + 1)) : MonomialOrder (Fin (n + 1)) :=
  prependWeight (prependWeight MonomialOrder.lex (otherWeight i)) Finsupp.degree

theorem variableLastOrder_exponent_antitone (i : Fin (n + 1))
    {a b : Fin (n + 1) →₀ ℕ} (hdeg : a.degree = b.degree)
    (hab : a ≼[variableLastOrder i] b) : b i ≤ a i := by
  rw [variableLastOrder, prependWeight_le_iff, hdeg] at hab
  have hother : otherWeight i a ≤ otherWeight i b := by
    have h := hab.resolve_left (lt_irrefl _)
    rw [prependWeight_le_iff] at h
    exact h.2.elim le_of_lt (fun h => h.1.le)
  have ha := otherWeight_add i a
  have hb := otherWeight_add i b
  omega

theorem leading_variable_exponent_le {K : Type*} [Field K]
    (i : Fin (n + 1)) {f : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n} {d : ℕ}
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) {a : Fin (n + 1) →₀ ℕ} (ha : a ∈ f.support) :
    (variableLastOrder i).degree f i ≤ a i := by
  apply variableLastOrder_exponent_antitone i
  · have hsupport := (Hilbert.MonomialBasis.GradedHilbert.mem_degreeSpace_iff_support f d).mp hf
    exact (hsupport a ha).trans (hsupport _ ((variableLastOrder i).degree_mem_support hf0)).symm
  · exact (variableLastOrder i).le_degree ha

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.WeightedOrder.GradedHilbert
