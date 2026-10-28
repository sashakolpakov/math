import OAI.AlgebraicGeometry.Comparison.Betti.SupportedTupleCochainMaps
import OAI.AlgebraicGeometry.Comparison.Betti.TupleCochainBoundary

/-! # Supported Cochain Sorting -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.SupportedCochainSorting.Cech

noncomputable section

section

/-! Signed sorting is homotopic to the identity on arbitrary supported additive cochains. -/

variable {ι V : Type} [LinearOrder ι] [AddCommGroup V]

def supportedCechSorting (N : Finset ι) (q : ℕ) :
    SupportedCochains.Cech.supportedCechCochains V N q →+ SupportedCochains.Cech.supportedCechCochains V N q :=
  SupportedTupleCochainMaps.Cech.supportedTupleCochainMap N q q (SheafCohomology.Projective.CechTupleAlternatingHomotopy.cechTupleAlternatingProjection q) (fun t =>
    SheafCohomology.Projective.CechTupleAlternatingHomotopy.cechTupleAlternatingProjection_supportedBy q (Finsupp.single t 1) (Set.range t)
      (SheafCohomology.Projective.CechTupleAlternatingHomotopy.CechTupleChain.supportedBy_single t 1 Set.Subset.rfl))

def supportedCechSortingHomotopy (N : Finset ι) (q : ℕ) :
    SupportedCochains.Cech.supportedCechCochains V N (q + 1) →+ SupportedCochains.Cech.supportedCechCochains V N q :=
  SupportedTupleCochainMaps.Cech.supportedTupleCochainMap N q (q + 1) (SheafCohomology.Projective.CechTupleAlternatingHomotopy.cechTupleAlternatingHomotopy q)
    (SheafCohomology.Projective.CechTupleAlternatingHomotopy.cechTupleAlternatingHomotopy_supportNonincreasing q)

theorem supportedCechSorting_homotopy (N : Finset ι) (q : ℕ)
    (s : SupportedCochains.Cech.supportedCechCochains V N (q + 1)) :
    SupportedCochains.Cech.supportedCechDifferential N q (supportedCechSortingHomotopy N q s) +
      supportedCechSortingHomotopy N (q + 1) (SupportedCochains.Cech.supportedCechDifferential N (q + 1) s) =
      supportedCechSorting N (q + 1) s - s := by
  apply Subtype.ext
  funext t
  let c : SheafCohomology.Projective.CechTupleAlternatingHomotopy.CechTupleChain ι (q + 1) := Finsupp.single t 1
  let L := TupleCochainBoundary.Cech.tupleCochainPairing (q + 1) s.val
  have hc : L c = s.val t := by
    change TupleCochainBoundary.Cech.tupleCochainPairing (q + 1) s.val (Finsupp.single t 1) = _
    rw [TupleCochainBoundary.Cech.tupleCochainPairing_single, one_smul]
  have h : L (SheafCohomology.Projective.CechTupleAlternatingHomotopy.cechTupleBoundary (q + 1) (SheafCohomology.Projective.CechTupleAlternatingHomotopy.cechTupleAlternatingHomotopy (q + 1) c)) +
      L (SheafCohomology.Projective.CechTupleAlternatingHomotopy.cechTupleAlternatingHomotopy q (SheafCohomology.Projective.CechTupleAlternatingHomotopy.cechTupleBoundary q c)) =
      L (SheafCohomology.Projective.CechTupleAlternatingHomotopy.cechTupleAlternatingProjection (q + 1) c) - L c :=
    (map_add L _ _).symm.trans ((congrArg L (SheafCohomology.Projective.CechTupleAlternatingHomotopy.cechTupleAlternatingHomotopy_identity (q + 1) c)).trans
      (map_sub L _ _))
  have hleft : (SupportedCochains.Cech.supportedCechDifferential N q (supportedCechSortingHomotopy N q s)).val t =
      L (SheafCohomology.Projective.CechTupleAlternatingHomotopy.cechTupleAlternatingHomotopy q (SheafCohomology.Projective.CechTupleAlternatingHomotopy.cechTupleBoundary q c)) := by
    have he : TupleCochainBoundary.Cech.tupleCochainPairing (q + 1)
        (SupportedCochains.Cech.supportedCechDifferential N q (supportedCechSortingHomotopy N q s)).val c =
        (SupportedCochains.Cech.supportedCechDifferential N q (supportedCechSortingHomotopy N q s)).val t := by
      change TupleCochainBoundary.Cech.tupleCochainPairing (q + 1) _ (Finsupp.single t 1) = _
      rw [TupleCochainBoundary.Cech.tupleCochainPairing_single, one_smul]
    exact he.symm.trans ((TupleCochainBoundary.Cech.tupleCochainPairing_boundary N q (supportedCechSortingHomotopy N q s) c).symm.trans
      (SupportedTupleCochainMaps.Cech.tupleCochainPairing_supportedMap N q (q + 1) (SheafCohomology.Projective.CechTupleAlternatingHomotopy.cechTupleAlternatingHomotopy q)
        (SheafCohomology.Projective.CechTupleAlternatingHomotopy.cechTupleAlternatingHomotopy_supportNonincreasing q) s (SheafCohomology.Projective.CechTupleAlternatingHomotopy.cechTupleBoundary q c)))
  have hright : (supportedCechSortingHomotopy N (q + 1)
      (SupportedCochains.Cech.supportedCechDifferential N (q + 1) s)).val t =
      L (SheafCohomology.Projective.CechTupleAlternatingHomotopy.cechTupleBoundary (q + 1) (SheafCohomology.Projective.CechTupleAlternatingHomotopy.cechTupleAlternatingHomotopy (q + 1) c)) :=
    (TupleCochainBoundary.Cech.tupleCochainPairing_boundary N (q + 1) s (SheafCohomology.Projective.CechTupleAlternatingHomotopy.cechTupleAlternatingHomotopy (q + 1) c)).symm
  exact (congrArg₂ (· + ·) hleft hright).trans
    ((add_comm _ _).trans (h.trans (congrArg (L (SheafCohomology.Projective.CechTupleAlternatingHomotopy.cechTupleAlternatingProjection (q + 1) c) - ·) hc)))

theorem supportedCechSorting_cycle (N : Finset ι) (q : ℕ)
    (s : SupportedCochains.Cech.supportedCechCochains V N (q + 1)) (hs : SupportedCochains.Cech.supportedCechDifferential N (q + 1) s = 0) :
    SupportedCochains.Cech.supportedCechDifferential N q (supportedCechSortingHomotopy N q s) =
      supportedCechSorting N (q + 1) s - s := by
  have h := supportedCechSorting_homotopy N q s
  rw [hs, map_zero, add_zero] at h
  exact h

end

/-! The signed sorting operator commutes with the actual supported differential. -/

variable {ι V : Type} [LinearOrder ι] [AddCommGroup V]

theorem supportedCechSorting_pairing (N : Finset ι) (q : ℕ)
    (s : SupportedCochains.Cech.supportedCechCochains V N q) (c : SheafCohomology.Projective.CechTupleAlternatingHomotopy.CechTupleChain ι q) :
    TupleCochainBoundary.Cech.tupleCochainPairing q (supportedCechSorting N q s).val c =
      TupleCochainBoundary.Cech.tupleCochainPairing q s.val (SheafCohomology.Projective.CechTupleAlternatingHomotopy.cechTupleAlternatingProjection q c) :=
  SupportedTupleCochainMaps.Cech.tupleCochainPairing_supportedMap N q q (SheafCohomology.Projective.CechTupleAlternatingHomotopy.cechTupleAlternatingProjection q) _ s c

theorem supportedCechSorting_differential (N : Finset ι) (q : ℕ)
    (s : SupportedCochains.Cech.supportedCechCochains V N q) :
    SupportedCochains.Cech.supportedCechDifferential N q (supportedCechSorting N q s) =
      supportedCechSorting N (q + 1) (SupportedCochains.Cech.supportedCechDifferential N q s) := by
  apply Subtype.ext
  funext t
  let c : SheafCohomology.Projective.CechTupleAlternatingHomotopy.CechTupleChain ι (q + 1) := Finsupp.single t 1
  have he : TupleCochainBoundary.Cech.tupleCochainPairing (q + 1)
      (SupportedCochains.Cech.supportedCechDifferential N q (supportedCechSorting N q s)).val c =
      (SupportedCochains.Cech.supportedCechDifferential N q (supportedCechSorting N q s)).val t := by
    change TupleCochainBoundary.Cech.tupleCochainPairing (q + 1) _ (Finsupp.single t 1) = _
    rw [TupleCochainBoundary.Cech.tupleCochainPairing_single, one_smul]
  exact he.symm.trans ((TupleCochainBoundary.Cech.tupleCochainPairing_boundary N q (supportedCechSorting N q s) c).symm.trans
    ((supportedCechSorting_pairing N q s (SheafCohomology.Projective.CechTupleAlternatingHomotopy.cechTupleBoundary q c)).trans
      ((congrArg (TupleCochainBoundary.Cech.tupleCochainPairing q s.val) (SheafCohomology.Projective.CechTupleAlternatingHomotopy.cechTupleAlternatingProjection_boundary q c).symm).trans
        (TupleCochainBoundary.Cech.tupleCochainPairing_boundary N q s (SheafCohomology.Projective.CechTupleAlternatingHomotopy.cechTupleAlternatingProjection (q + 1) c)))))

theorem supportedCechSorting_zero_degree (N : Finset ι) (s : SupportedCochains.Cech.supportedCechCochains V N 0) :
    supportedCechSorting N 0 s = s := by
  apply Subtype.ext
  funext t
  change TupleCochainBoundary.Cech.tupleCochainPairing 0 s.val (SheafCohomology.Projective.CechTupleAlternatingHomotopy.cechTupleAlternatingProjection 0 (Finsupp.single t 1)) = s.val t
  rw [SheafCohomology.Projective.CechTupleAlternatingHomotopy.cechTupleAlternatingProjection_zero, TupleCochainBoundary.Cech.tupleCochainPairing_single, one_smul]

end

end OAI.AlgebraicGeometry.Comparison.Betti.SupportedCochainSorting.Cech
