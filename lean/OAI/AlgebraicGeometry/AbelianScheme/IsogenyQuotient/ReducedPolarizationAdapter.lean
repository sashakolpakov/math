import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ReducedGroupRigidity
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PolarizationPoincareComparison
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.RelativeAnnihilator

/-! # Reduced Polarization Adapter -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction

noncomputable section

/-!
The original HilbertConstruction polarization gives the actual CartierDuality polarization on a
reduced locally Noetherian base. All subsequent pairing and annihilator
statements retain arbitrary parameter and test schemes, including
nonreduced ones. The reduced-base hypothesis is confined to deriving
compatibility of the original dual group law with Picard tensor product.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

universe u

variable {S : Scheme.{u}} [IsReduced S] [IsLocallyNoetherian S] {g : ℕ}
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ)

set_option backward.isDefEq.respectTransparency false in
theorem originalPolarization_preserves_canonical_group_over_reduced_base :
    IsMonHom (show A.scheme ⟶ (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).withPicardGroup.abelian from pol.isogeny.hom) := by
  change @IsMonHom _ _ _ _ _ A.group.toMonObj
    (Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D)).toMonObj pol.isogeny.hom
  rw [ReducedGroupRigidity.Construction.dualPicardGroup_eq_given_over_reduced_base]
  exact pol.isogeny.preservesGroup

def reducedBasePolarizationOfHilbertConstruction : CartierDuality.PolarizedTorsion.Polarization (PolarizationPoincareComparison.Construction.nativeAbelianOfHilbertConstruction A) where
  representation := Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D
  map := pol.isogeny.hom
  preservesGroup := originalPolarization_preserves_canonical_group_over_reduced_base A D pol
  finite := pol.isogeny.finite
  flat := pol.isogeny.flat
  surjective := pol.isogeny.surjective
  positive K _ _ s := PolarizationPoincareComparison.Construction.canonicalPositiveOnGeometricFiber_ofHilbertConstruction A D pol.isogeny.hom K s (pol.positive K s)

theorem reducedBasePolarizationOfHilbertConstruction_map :
    (reducedBasePolarizationOfHilbertConstruction A D pol).map = pol.isogeny.hom := rfl

theorem reducedBasePolarizationOfHilbertConstruction_poincare :
    (reducedBasePolarizationOfHilbertConstruction A D pol).dual.poincare = D.poincare := rfl

theorem reducedBasePolarizationOfHilbertConstruction_fiberDegree (s : S) :
    (reducedBasePolarizationOfHilbertConstruction A D pol).fiberDegree s = (∏ i, δ i) ^ 2 :=
  pol.kernelType.degree _

def reducedBaseNativePolarizationPairing (n : ℕ) (hn : 0 < n) :
    Annihilator.Construction.SchemeBicharacter (A := Torsion.Groups.Construction.nativeTorsionScheme A.scheme n)
      (B := Torsion.Groups.Construction.nativeTorsionScheme A.scheme n)
      (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X) :=
  Canonical.RelativePairing.Construction.canonicalNativePolarizationPairing (reducedBasePolarizationOfHilbertConstruction A D pol) n hn

theorem reducedBaseNativePolarizationPairing_isPerfect (n : ℕ) (hn : 0 < n)
    (hdegree : Nat.Coprime n ((∏ i, δ i) ^ 2)) :
    (reducedBaseNativePolarizationPairing A D pol n hn).toSheafPairing.IsPerfect := by
  apply Canonical.RelativePairing.Construction.canonicalNativePolarizationPairing_isPerfect
  intro s
  rw [reducedBasePolarizationOfHilbertConstruction_fiberDegree]
  exact hdegree

theorem reducedBaseNativePolarization_relative_double_annihilator
    (n : ℕ) (hn : 0 < n) (hdegree : Nat.Coprime n ((∏ i, δ i) ^ 2))
    (P : Over S) (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup (Torsion.Groups.Construction.nativeTorsionScheme A.scheme n) P) (R : F.Model) :
    let e := reducedBaseNativePolarizationPairing A D pol n hn
    e.flip.relativeAnnihilator (e.relativeAnnihilator F) = F := by
  exact Canonical.RelativeAnnihilator.Construction.canonicalPolarization_relative_double_annihilator (reducedBasePolarizationOfHilbertConstruction A D pol) n hn
    (fun s => (reducedBasePolarizationOfHilbertConstruction_fiberDegree A D pol s).symm ▸ hdegree) P F R

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction
