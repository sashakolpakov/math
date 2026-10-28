import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.WeilPairing
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FiberPolarizationType

/-! # Geometric Torsion Pairing -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricTorsionPairing

noncomputable section

/-! Construct the finite-level pairing of the actual PEL polarization
from the committed IsogenyQuotient inverse Cartier-to-Picard map. Its perfection
is proved from the original polarization degree at the good prime. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

variable {R k : Type} [CommRing R] [Field k] [IsAlgClosed k] {g N : ℕ}
  (P : PEL.PELFamilyData R g N (Spec (.of k)))
  (δ : Fin g → ℕ) (hδ : P.polarizationMap.HasPolarizationType δ)
  (q : ℕ) [Fact q.Prime] (hq : Nat.Coprime q (∏ i, δ i)) (m : ℕ)

private instance polarization_givenGroup_isMonHom :
    IsMonHom (show P.abelian.scheme ⟶ (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled P.dual).abelian from P.polarizationMap.hom) :=
  P.polarizationMap.preservesGroup

private instance polarization_givenGroup_finite :
    IsFinite (show P.abelian.scheme ⟶ (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled P.dual).abelian from P.polarizationMap.hom).left :=
  P.polarizationMap.finite

private instance polarization_givenGroup_flat :
    Flat (show P.abelian.scheme ⟶ (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled P.dual).abelian from P.polarizationMap.hom).left :=
  P.polarizationMap.flat

private instance polarization_givenGroup_surjective :
    Surjective (show P.abelian.scheme ⟶ (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled P.dual).abelian from P.polarizationMap.hom).left :=
  P.polarizationMap.surjective

include hδ hq in
omit [IsAlgClosed k] [Fact q.Prime] in
private theorem torsionPairing_coprime_degree (s : Spec (.of k)) :
    (q ^ m).Coprime (P.polarizationMap.hom.left.finrank (η[P.dual.abelian.scheme].left s)) := by
  rw [hδ.degree]
  exact (hq.pow_left m).pow_right 2

def pelGeometricTorsionPairing :
    IsogenyQuotient.Annihilator.Construction.SchemeBicharacter
      (A := IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme P.abelian.scheme (q ^ m))
      (B := IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme P.abelian.scheme (q ^ m))
      (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of k))).X) :=
  IsogenyQuotient.Geometric.WeilPairing.Construction.geometricIsogenyTorsionPairing P.abelian.scheme (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled P.dual)
    P.polarizationMap.hom (q ^ m) (pow_pos (Fact.out : q.Prime).pos m)
    (torsionPairing_coprime_degree P δ hδ q hq m)

theorem pelGeometricTorsionPairing_isPerfect :
    (pelGeometricTorsionPairing P δ hδ q hq m).toSheafPairing.IsPerfect :=
  IsogenyQuotient.Geometric.WeilPairing.Construction.geometricIsogenyTorsionPairing_isPerfect P.abelian.scheme (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled P.dual)
    P.polarizationMap.hom (q ^ m) (pow_pos (Fact.out : q.Prime).pos m)
    (torsionPairing_coprime_degree P δ hδ q hq m)

namespace SphericalPELAlbaneseData
variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.IsGoodCompletelySplitPrime)
  (hgeometry : D.HasIntegralModelGeometry) {k : Type} [Field k] [IsAlgClosed k]
  (b : Spec (.of k) ⟶ Spec (.of K)) (x : D.GeometricPoint b) (m : ℕ)

def _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.geometricTorsionPairing :=
  pelGeometricTorsionPairing (D.fiberFamily b x) D.reference.polarizationType
    (D.fiberPolarizationType hgeometry b x) q hg.2.2.2.2 m

theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.geometricTorsionPairing_isPerfect :
    (D.geometricTorsionPairing hg hgeometry b x m).toSheafPairing.IsPerfect :=
  pelGeometricTorsionPairing_isPerfect (D.fiberFamily b x) D.reference.polarizationType
    (D.fiberPolarizationType hgeometry b x) q hg.2.2.2.2 m

end SphericalPELAlbaneseData

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricTorsionPairing
