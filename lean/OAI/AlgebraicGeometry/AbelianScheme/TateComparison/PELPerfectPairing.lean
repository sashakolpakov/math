import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.WeilValues
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricWeilNondegeneracy
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PadicPairingPerfection
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricLattice

/-! # PEL Perfect Pairing -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELPerfectPairing

noncomputable section

/-! The actual PEL polarization constructs a perfect integral pairing
on its geometric Tate module at every good prime. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

theorem padic_first_residue_zero (q : ℕ) [Fact q.Prime] (a : ℤ_[q])
    (ha : PadicInt.toZMod a = 0) : PadicInt.toZModPow 1 a = 0 := by
  apply RingHom.mem_ker.mp
  rw [PadicInt.ker_toZModPow, pow_one, ← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod]
  exact RingHom.mem_ker.mpr ha

variable {R k : Type} [CommRing R] [Field k] [CharZero k] [IsAlgClosed k] {g N : ℕ}
  (P : PEL.PELFamilyData R g N (Spec (.of k)))
  (δ : Fin g → ℕ) (hδ : P.polarizationMap.HasPolarizationType δ)
  (q : ℕ) [Fact q.Prime] (hq : Nat.Coprime q (∏ i, δ i))

private instance polarization_group :
    IsMonHom (show P.abelian.scheme ⟶ (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled P.dual).abelian from P.polarizationMap.hom) :=
  P.polarizationMap.preservesGroup

private instance polarization_finite :
    IsFinite (show P.abelian.scheme ⟶ (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled P.dual).abelian from P.polarizationMap.hom).left :=
  P.polarizationMap.finite

private instance polarization_flat :
    Flat (show P.abelian.scheme ⟶ (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled P.dual).abelian from P.polarizationMap.hom).left :=
  P.polarizationMap.flat

private instance polarization_surjective :
    Surjective (show P.abelian.scheme ⟶ (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled P.dual).abelian from P.polarizationMap.hom).left :=
  P.polarizationMap.surjective

include hδ hq in
omit [CharZero k] [IsAlgClosed k] [Fact q.Prime] in
private theorem pelWeilDegree (n : ℕ) (s : Spec (.of k)) :
    (q ^ n).Coprime (P.polarizationMap.hom.left.finrank (η[P.dual.abelian.scheme].left s)) := by
  rw [hδ.degree]
  exact (hq.pow_left n).pow_right 2

def pelTateWeilPairing :=
  WeilValues.isogenyTateWeilPairing P.abelian.scheme (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled P.dual) P.polarizationMap.hom q
    (pelWeilDegree P δ hδ q hq)

theorem pelTateWeilPairing_spec
    (v w : Add.schemeTateModule P.abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q) (n : ℕ) :
    PadicInt.toZModPow n (pelTateWeilPairing P δ hδ q hq v w) =
      TorsionPairingCoordinates.tateBicharacterResidues P.abelian.scheme P.abelian.scheme q n
        (GeometricTorsionPairing.pelGeometricTorsionPairing P δ hδ q hq n) v w :=
  WeilValues.isogenyTateWeilPairing_spec P.abelian.scheme (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled P.dual) P.polarizationMap.hom q
    (pelWeilDegree P δ hδ q hq) v w n

namespace SphericalPELAlbaneseData

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.IsGoodCompletelySplitPrime)
  (hgeometry : D.HasIntegralModelGeometry) {k : Type} [Field k] [CharZero k] [IsAlgClosed k]
  (b : Spec (.of k) ⟶ Spec (.of K)) (x : D.GeometricPoint b)

def _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.geometricTateWeilPairing :=
  pelTateWeilPairing (D.fiberFamily b x) D.reference.polarizationType
    (D.fiberPolarizationType hgeometry b x) q hg.2.2.2.2

theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.geometricTateWeilPairing_spec
    (v w : Add.schemeTateModule (D.fiberFamily b x).abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q) (n : ℕ) :
    PadicInt.toZModPow n (D.geometricTateWeilPairing hg hgeometry b x v w) =
      D.geometricWeilResidues hg hgeometry b x n v w :=
  pelTateWeilPairing_spec (D.fiberFamily b x) D.reference.polarizationType
    (D.fiberPolarizationType hgeometry b x) q hg.2.2.2.2 v w n

theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.geometricTateWeilPairing_isPerfect :
    (D.geometricTateWeilPairing hg hgeometry b x).IsPerfPair := by
  apply PadicPairingPerfection.padic_pairing_perfect_of_reduction_detection q
    (GeometricLattice.geometricTateBasis (D.fiberFamily b x).abelian q) (GeometricLattice.geometricTateBasis (D.fiberFamily b x).abelian q)
  intro v hv
  have he : Evaluation.Tate.evaluate q 1 v = 0 := by
    apply D.geometricWeilResidues_detects_evaluation hg hgeometry b x 1 v
    intro w
    exact (D.geometricTateWeilPairing_spec hg hgeometry b x v w 1).symm.trans
      (padic_first_residue_zero q _ (hv w))
  obtain ⟨z, hz⟩ := (Evaluation.Tate.evaluate_eq_zero_iff q 1 v).mp he
  exact ⟨z, by simpa only [pow_one] using hz⟩

end SphericalPELAlbaneseData

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELPerfectPairing
