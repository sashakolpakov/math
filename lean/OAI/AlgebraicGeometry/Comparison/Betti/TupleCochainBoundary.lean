import OAI.AlgebraicGeometry.Comparison.Betti.SupportedCochains
import OAI.AlgebraicGeometry.SheafCohomology.Projective.CechTupleAlternatingHomotopy

/-! # Tuple Cochain Boundary -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.TupleCochainBoundary.Cech

noncomputable section

section

/-! Pair arbitrary additive cochains with the actual finite integral tuple chains. -/

open scoped BigOperators

open OAI.AlgebraicGeometry.SheafCohomology.Projective.CechTupleAlternatingHomotopy

variable {ι V : Type} [AddCommGroup V]

def tupleCochainPairing (q : ℕ) (s : (Fin (q + 1) → ι) → V) : SheafCohomology.Projective.CechTupleAlternatingHomotopy.CechTupleChain ι q →ₗ[ℤ] V :=
  Finsupp.lsum ℤ (fun t => LinearMap.toSpanSingleton ℤ V (s t))

theorem tupleCochainPairing_sum (q : ℕ) (s : (Fin (q + 1) → ι) → V) (c : SheafCohomology.Projective.CechTupleAlternatingHomotopy.CechTupleChain ι q) :
    tupleCochainPairing q s c = ∑ t ∈ c.support, c t • s t := rfl

theorem tupleCochainPairing_single (q : ℕ) (s : (Fin (q + 1) → ι) → V)
    (t : Fin (q + 1) → ι) (a : ℤ) : tupleCochainPairing q s (Finsupp.single t a) = a • s t := by
  simp [tupleCochainPairing]

theorem tupleCochainPairing_zero (q : ℕ) (c : SheafCohomology.Projective.CechTupleAlternatingHomotopy.CechTupleChain ι q) :
    tupleCochainPairing q (0 : (Fin (q + 1) → ι) → V) c = 0 := by
  rw [tupleCochainPairing_sum]
  simp only [Pi.zero_apply, smul_zero, Finset.sum_const_zero]

theorem tupleCochainPairing_add (q : ℕ) (s t : (Fin (q + 1) → ι) → V) (c : SheafCohomology.Projective.CechTupleAlternatingHomotopy.CechTupleChain ι q) :
    tupleCochainPairing q (s + t) c = tupleCochainPairing q s c + tupleCochainPairing q t c := by
  rw [tupleCochainPairing_sum, tupleCochainPairing_sum, tupleCochainPairing_sum]
  simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]

variable [DecidableEq ι]

omit [DecidableEq ι] in
theorem supportCechDelete_eq_tupleDelete {q : ℕ} (t : Fin (q + 2) → ι) (k : Fin (q + 2)) :
    SupportedCochains.Cech.supportCechDelete t k = SheafCohomology.Projective.CechTupleAlternatingHomotopy.cechTupleDelete t k := rfl

theorem tupleCochainPairing_supported_zero (N : Finset ι) (q : ℕ)
    (s : SupportedCochains.Cech.supportedCechCochains V N q) {r : ℕ} (t : Fin (r + 1) → ι)
    (c : SheafCohomology.Projective.CechTupleAlternatingHomotopy.CechTupleChain ι q) (hc : SheafCohomology.Projective.CechTupleAlternatingHomotopy.CechTupleChain.SupportedBy c (Set.range t))
    (ht : ¬N ⊆ Finset.univ.image t) : tupleCochainPairing q s.val c = 0 := by
  rw [tupleCochainPairing_sum]
  apply Finset.sum_eq_zero
  intro a ha
  have hna : ¬N ⊆ Finset.univ.image a := by
    intro hN
    apply ht
    intro j hj
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp (hN hj)
    obtain ⟨l, hl⟩ := hc ha ⟨k, hk⟩
    exact Finset.mem_image.mpr ⟨l, Finset.mem_univ _, hl⟩
  rw [s.property a hna, smul_zero]

end

/-! Pairing identifies the original additive coboundary with the integral tuple boundary. -/

open scoped BigOperators

open OAI.AlgebraicGeometry.SheafCohomology.Projective.CechTupleAlternatingHomotopy

variable {ι V : Type} [DecidableEq ι] [AddCommGroup V]

theorem tupleCochainPairing_boundaryBasis (N : Finset ι) (q : ℕ)
    (s : SupportedCochains.Cech.supportedCechCochains V N q) (t : Fin (q + 2) → ι) :
    tupleCochainPairing q s.val (SheafCohomology.Projective.CechTupleAlternatingHomotopy.cechTupleBoundaryBasis q t) =
      (SupportedCochains.Cech.supportedCechDifferential N q s).val t := by
  change tupleCochainPairing q s.val (∑ k : Fin (q + 2),
      Finsupp.single (SheafCohomology.Projective.CechTupleAlternatingHomotopy.cechTupleDelete t k) ((-1 : ℤ) ^ k.val)) =
    ∑ k : Fin (q + 2), (-1 : ℤ) ^ k.val • s.val (SupportedCochains.Cech.supportCechDelete t k)
  exact (map_sum (tupleCochainPairing q s.val) _ Finset.univ).trans
    (Finset.sum_congr rfl (fun k _ => tupleCochainPairing_single q s.val (SheafCohomology.Projective.CechTupleAlternatingHomotopy.cechTupleDelete t k) _))

theorem tupleCochainPairing_boundary (N : Finset ι) (q : ℕ)
    (s : SupportedCochains.Cech.supportedCechCochains V N q) (c : SheafCohomology.Projective.CechTupleAlternatingHomotopy.CechTupleChain ι (q + 1)) :
    tupleCochainPairing q s.val (SheafCohomology.Projective.CechTupleAlternatingHomotopy.cechTupleBoundary q c) =
      tupleCochainPairing (q + 1) (SupportedCochains.Cech.supportedCechDifferential N q s).val c := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c e hc he => simp only [map_add, hc, he]
  | single t a =>
    rw [SheafCohomology.Projective.CechTupleAlternatingHomotopy.cechTupleBoundary_single, map_smul, tupleCochainPairing_single]
    exact congrArg (a • ·) (tupleCochainPairing_boundaryBasis N q s t)

end

end OAI.AlgebraicGeometry.Comparison.Betti.TupleCochainBoundary.Cech
