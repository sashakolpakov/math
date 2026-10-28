import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.GroupRigidity
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PolarizationPoincareComparison
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.RelativePairing

/-! # Polarization Adapter -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.PolarizationAdapter.Construction

noncomputable section

/-!
Over every field, the original HilbertConstruction polarization supplies CartierDuality's complete
geometric polarization object. Its scheme, map, normalized Poincare
bundle, ampleness and actual degree are preserved. No perfect pairing
or compatibility of two independently given group laws is an input.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

universe u

variable {k : Type u} [Field k] {g : ℕ}
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ)

set_option backward.isDefEq.respectTransparency false in
theorem originalPolarization_preserves_canonical_group_over_field :
    IsMonHom (show A.scheme ⟶ (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).withPicardGroup.abelian from pol.isogeny.hom) := by
  change @IsMonHom _ _ _ _ _ A.group.toMonObj
    (Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D)).toMonObj pol.isogeny.hom
  rw [GroupRigidity.Construction.dualPicardGroup_eq_given_over_field]
  exact pol.isogeny.preservesGroup

def fieldPolarizationOfHilbertConstruction : CartierDuality.PolarizedTorsion.Polarization (PolarizationPoincareComparison.Construction.nativeAbelianOfHilbertConstruction A) where
  representation := Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D
  map := pol.isogeny.hom
  preservesGroup := originalPolarization_preserves_canonical_group_over_field A D pol
  finite := pol.isogeny.finite
  flat := pol.isogeny.flat
  surjective := pol.isogeny.surjective
  positive K _ _ s := PolarizationPoincareComparison.Construction.canonicalPositiveOnGeometricFiber_ofHilbertConstruction A D pol.isogeny.hom K s (pol.positive K s)

theorem fieldPolarizationOfHilbertConstruction_map : (fieldPolarizationOfHilbertConstruction A D pol).map = pol.isogeny.hom := rfl

theorem fieldPolarizationOfHilbertConstruction_poincare :
    (fieldPolarizationOfHilbertConstruction A D pol).dual.poincare = D.poincare := rfl

theorem fieldPolarizationOfHilbertConstruction_fiberDegree (s : Spec (.of k)) :
    (fieldPolarizationOfHilbertConstruction A D pol).fiberDegree s = (∏ i, δ i) ^ 2 :=
  pol.kernelType.degree _

def fieldNativePolarizationPairing (n : ℕ) (hn : 0 < n) :
    Annihilator.Construction.SchemeBicharacter (A := Torsion.Groups.Construction.nativeTorsionScheme A.scheme n)
      (B := Torsion.Groups.Construction.nativeTorsionScheme A.scheme n)
      (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of k))).X) :=
  Canonical.RelativePairing.Construction.canonicalNativePolarizationPairing (fieldPolarizationOfHilbertConstruction A D pol) n hn

theorem fieldNativePolarizationPairing_isPerfect (n : ℕ) (hn : 0 < n)
    (hdegree : Nat.Coprime n ((∏ i, δ i) ^ 2)) :
    (fieldNativePolarizationPairing A D pol n hn).toSheafPairing.IsPerfect := by
  apply Canonical.RelativePairing.Construction.canonicalNativePolarizationPairing_isPerfect
  intro s
  rw [fieldPolarizationOfHilbertConstruction_fiberDegree]
  exact hdegree

theorem fieldNativePolarizationPairing_qpower_isPerfect
    (q h : ℕ) (hq : q.Prime) (hdegree : Nat.Coprime q ((∏ i, δ i) ^ 2)) :
    (fieldNativePolarizationPairing A D pol (q ^ h) (pow_pos hq.pos h)).toSheafPairing.IsPerfect :=
  fieldNativePolarizationPairing_isPerfect A D pol (q ^ h) (pow_pos hq.pos h) (hdegree.pow_left h)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.PolarizationAdapter.Construction
