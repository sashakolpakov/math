import OAI.AlgebraicGeometry.Comparison.Betti.TupleCochainBoundary

/-! # Supported Tuple Cochain Maps -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.SupportedTupleCochainMaps.Cech

noncomputable section

/-! Support-preserving finite tuple-chain maps act on arbitrary additive cochains. -/

variable {ι V : Type} [DecidableEq ι] [AddCommGroup V]

def supportedTupleCochainMap (N : Finset ι) (q r : ℕ)
    (F : SheafCohomology.Projective.CechTupleAlternatingHomotopy.CechTupleChain ι q →ₗ[ℤ] SheafCohomology.Projective.CechTupleAlternatingHomotopy.CechTupleChain ι r) (hF : SheafCohomology.Projective.CechTupleAlternatingHomotopy.CechTupleSupportNonincreasing F) :
    SupportedCochains.Cech.supportedCechCochains V N r →+ SupportedCochains.Cech.supportedCechCochains V N q where
  toFun s := ⟨fun t => TupleCochainBoundary.Cech.tupleCochainPairing r s.val (F (Finsupp.single t 1)),
    fun t ht => TupleCochainBoundary.Cech.tupleCochainPairing_supported_zero N r s t _ (hF t) ht⟩
  map_zero' := by
    apply Subtype.ext
    funext t
    exact TupleCochainBoundary.Cech.tupleCochainPairing_zero r _
  map_add' s t := by
    apply Subtype.ext
    funext a
    exact TupleCochainBoundary.Cech.tupleCochainPairing_add r s.val t.val _

theorem supportedTupleCochainMap_apply (N : Finset ι) (q r : ℕ)
    (F : SheafCohomology.Projective.CechTupleAlternatingHomotopy.CechTupleChain ι q →ₗ[ℤ] SheafCohomology.Projective.CechTupleAlternatingHomotopy.CechTupleChain ι r) (hF : SheafCohomology.Projective.CechTupleAlternatingHomotopy.CechTupleSupportNonincreasing F)
    (s : SupportedCochains.Cech.supportedCechCochains V N r) (t : Fin (q + 1) → ι) :
    (supportedTupleCochainMap N q r F hF s).val t = TupleCochainBoundary.Cech.tupleCochainPairing r s.val (F (Finsupp.single t 1)) := rfl

theorem tupleCochainPairing_supportedMap (N : Finset ι) (q r : ℕ)
    (F : SheafCohomology.Projective.CechTupleAlternatingHomotopy.CechTupleChain ι q →ₗ[ℤ] SheafCohomology.Projective.CechTupleAlternatingHomotopy.CechTupleChain ι r) (hF : SheafCohomology.Projective.CechTupleAlternatingHomotopy.CechTupleSupportNonincreasing F)
    (s : SupportedCochains.Cech.supportedCechCochains V N r) (c : SheafCohomology.Projective.CechTupleAlternatingHomotopy.CechTupleChain ι q) :
    TupleCochainBoundary.Cech.tupleCochainPairing q (supportedTupleCochainMap N q r F hF s).val c =
      TupleCochainBoundary.Cech.tupleCochainPairing r s.val (F c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c e hc he => simp only [map_add, hc, he]
  | single t a =>
    rw [TupleCochainBoundary.Cech.tupleCochainPairing_single]
    change a • TupleCochainBoundary.Cech.tupleCochainPairing r s.val (F (Finsupp.single t 1)) =
      TupleCochainBoundary.Cech.tupleCochainPairing r s.val (F (Finsupp.single t a))
    have ha : Finsupp.single t a = a • Finsupp.single t (1 : ℤ) := by simp [Finsupp.smul_single]
    exact ((TupleCochainBoundary.Cech.tupleCochainPairing r s.val).map_smul a (F (Finsupp.single t 1))).symm.trans
      (congrArg (TupleCochainBoundary.Cech.tupleCochainPairing r s.val)
        ((F.map_smul a (Finsupp.single t 1)).symm.trans (congrArg F ha.symm)))

end

end OAI.AlgebraicGeometry.Comparison.Betti.SupportedTupleCochainMaps.Cech
