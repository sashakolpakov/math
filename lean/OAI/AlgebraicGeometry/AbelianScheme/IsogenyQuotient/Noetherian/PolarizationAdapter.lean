import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.GroupRigidity
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PolarizationPoincareComparison
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.RelativePairing

/-! # Polarization Adapter -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.PolarizationAdapter.Construction

noncomputable section

/-! The original HilbertConstruction polarization supplies CartierDuality's native polarization
over every locally Noetherian base, preserving its Poincare line and actual degree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

variable {S : Scheme.{0}} [IsLocallyNoetherian S] {g : ℕ}
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ)

set_option backward.isDefEq.respectTransparency false in
theorem originalPolarization_preserves_canonical_group_over_noetherian_base :
    IsMonHom (show A.scheme ⟶ (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).withPicardGroup.abelian from pol.isogeny.hom) := by
  change @IsMonHom _ _ _ _ _ A.group.toMonObj
    (Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D)).toMonObj pol.isogeny.hom
  rw [GroupRigidity.Construction.dualPicardGroup_eq_given_over_noetherian_base]
  exact pol.isogeny.preservesGroup

def noetherianPolarizationOfHilbertConstruction : CartierDuality.PolarizedTorsion.Polarization (PolarizationPoincareComparison.Construction.nativeAbelianOfHilbertConstruction A) where
  representation := Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D
  map := pol.isogeny.hom
  preservesGroup := originalPolarization_preserves_canonical_group_over_noetherian_base A D pol
  finite := pol.isogeny.finite
  flat := pol.isogeny.flat
  surjective := pol.isogeny.surjective
  positive K _ _ s := PolarizationPoincareComparison.Construction.canonicalPositiveOnGeometricFiber_ofHilbertConstruction A D pol.isogeny.hom K s (pol.positive K s)

theorem noetherianPolarizationOfHilbertConstruction_map :
    (noetherianPolarizationOfHilbertConstruction A D pol).map = pol.isogeny.hom := rfl

theorem noetherianPolarizationOfHilbertConstruction_poincare :
    (noetherianPolarizationOfHilbertConstruction A D pol).dual.poincare = D.poincare := rfl

theorem noetherianPolarizationOfHilbertConstruction_fiberDegree (s : S) :
    (noetherianPolarizationOfHilbertConstruction A D pol).fiberDegree s = (∏ i, δ i) ^ 2 :=
  pol.kernelType.degree _

def noetherianNativePolarizationPairing (n : ℕ) (hn : 0 < n) :
    Annihilator.Construction.SchemeBicharacter (A := Torsion.Groups.Construction.nativeTorsionScheme A.scheme n)
      (B := Torsion.Groups.Construction.nativeTorsionScheme A.scheme n)
      (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X) :=
  Canonical.RelativePairing.Construction.canonicalNativePolarizationPairing (noetherianPolarizationOfHilbertConstruction A D pol) n hn

theorem noetherianNativePolarizationPairing_isPerfect (n : ℕ) (hn : 0 < n)
    (hdegree : Nat.Coprime n ((∏ i, δ i) ^ 2)) :
    (noetherianNativePolarizationPairing A D pol n hn).toSheafPairing.IsPerfect := by
  apply Canonical.RelativePairing.Construction.canonicalNativePolarizationPairing_isPerfect
  intro s
  rw [noetherianPolarizationOfHilbertConstruction_fiberDegree]
  exact hdegree

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.PolarizationAdapter.Construction
