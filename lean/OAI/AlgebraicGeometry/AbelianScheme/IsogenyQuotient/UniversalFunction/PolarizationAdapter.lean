import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.GroupRigidity
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PolarizationPoincareComparison
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.RelativePairing

/-! # Polarization Adapter -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.PolarizationAdapter.Construction

noncomputable section

/-! Universal functions on the original dual identify its native group
with the Picard group, preserving the actual HilbertConstruction polarization and Poincare line. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

variable {S : Scheme.{0}} {g : ℕ}
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ)
  (hD : GlobalFunctions.Construction.HasUniversalGlobalFunctions D.abelian.scheme)

include hD in
set_option backward.isDefEq.respectTransparency false in
theorem originalPolarization_preserves_canonical_group_of_universal_functions :
    IsMonHom (show A.scheme ⟶ (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).withPicardGroup.abelian from pol.isogeny.hom) := by
  change @IsMonHom _ _ _ _ _ A.group.toMonObj
    (Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D)).toMonObj pol.isogeny.hom
  rw [GroupRigidity.Construction.dualPicardGroup_eq_given_of_universal_functions (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D) hD]
  exact pol.isogeny.preservesGroup

def universalFunctionPolarizationOfHilbertConstruction : CartierDuality.PolarizedTorsion.Polarization (PolarizationPoincareComparison.Construction.nativeAbelianOfHilbertConstruction A) where
  representation := Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D
  map := pol.isogeny.hom
  preservesGroup := originalPolarization_preserves_canonical_group_of_universal_functions A D pol hD
  finite := pol.isogeny.finite
  flat := pol.isogeny.flat
  surjective := pol.isogeny.surjective
  positive K _ _ s := PolarizationPoincareComparison.Construction.canonicalPositiveOnGeometricFiber_ofHilbertConstruction A D pol.isogeny.hom K s (pol.positive K s)

theorem universalFunctionPolarizationOfHilbertConstruction_map :
    (universalFunctionPolarizationOfHilbertConstruction A D pol hD).map = pol.isogeny.hom := rfl

theorem universalFunctionPolarizationOfHilbertConstruction_poincare :
    (universalFunctionPolarizationOfHilbertConstruction A D pol hD).dual.poincare = D.poincare := rfl

theorem universalFunctionPolarizationOfHilbertConstruction_fiberDegree (s : S) :
    (universalFunctionPolarizationOfHilbertConstruction A D pol hD).fiberDegree s = (∏ i, δ i) ^ 2 :=
  pol.kernelType.degree _

def universalFunctionNativePolarizationPairing (n : ℕ) (hn : 0 < n) :
    Annihilator.Construction.SchemeBicharacter (A := Torsion.Groups.Construction.nativeTorsionScheme A.scheme n)
      (B := Torsion.Groups.Construction.nativeTorsionScheme A.scheme n)
      (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X) :=
  Canonical.RelativePairing.Construction.canonicalNativePolarizationPairing (universalFunctionPolarizationOfHilbertConstruction A D pol hD) n hn

theorem universalFunctionNativePolarizationPairing_isPerfect (n : ℕ) (hn : 0 < n)
    (hdegree : Nat.Coprime n ((∏ i, δ i) ^ 2)) :
    (universalFunctionNativePolarizationPairing A D pol hD n hn).toSheafPairing.IsPerfect := by
  apply Canonical.RelativePairing.Construction.canonicalNativePolarizationPairing_isPerfect
  intro s
  rw [universalFunctionPolarizationOfHilbertConstruction_fiberDegree]
  exact hdegree

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.PolarizationAdapter.Construction
