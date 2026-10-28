import OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.BundledDual
import OAI.AlgebraicGeometry.Picard.PoincareBundle.WeilCanonicalTorsionPairing
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Reference.PairingIndependence

/-! # Weil Pairing -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Reference.WeilPairing

noncomputable section

/-! The actual standard Weil pairing supplies self-annihilation for the original Poincare descent construction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Reference.Symmetry.ReferencePoincare OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.BundledDual

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  (ell : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A D.abelian) (n : ℕ) (hn : 0 < n)
  [IsFinite ((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n).left]
  [Flat ((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n).left]
  [Surjective ((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n).left]
  [LocallyOfFinitePresentation ((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n).left]
  [IsAffine (Kernel.Scheme.kernelObject ((𝟙 A.scheme) ^ n)).left]
  (C : AbelianScheme.CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation (Spec (.of k))
    (Grp.mk (Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.scheme) ^ n))))

/-- The given isogeny defines the actual standard Weil value after the dual-group comparison. -/
def value {T : Over (Spec (.of k))} (x y : T ⟶ Kernel.Scheme.kernelObject ((𝟙 A.scheme) ^ n)) :
    (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.multiplicativeFppfAb (Spec (.of k))).obj.obj (.op T) := by
  have : IsMonHom (show A.scheme ⟶ (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).withPicardGroup.abelian from
      (Canonical.BundledDual.isogeny D ell).hom) := (Canonical.BundledDual.isogeny D ell).preservesGroup
  have : IsFinite (show A.scheme ⟶ (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).withPicardGroup.abelian from
      (Canonical.BundledDual.isogeny D ell).hom).left := (Canonical.BundledDual.isogeny D ell).finite
  have : Flat (show A.scheme ⟶ (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).withPicardGroup.abelian from
      (Canonical.BundledDual.isogeny D ell).hom).left := (Canonical.BundledDual.isogeny D ell).flat
  have : Surjective (show A.scheme ⟶ (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).withPicardGroup.abelian from
      (Canonical.BundledDual.isogeny D ell).hom).left := (Canonical.BundledDual.isogeny D ell).surjective
  exact WeilCanonicalTorsionPairing.weilValue A (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D) (Canonical.BundledDual.isogeny D ell).hom n hn C x y

variable (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)
  (hformula : Nonempty (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule
    (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared D.poincare) ell.hom).sheaf
      (L.pullback (fst A.scheme A.scheme).left).sheaf)
    (L.pullback (snd A.scheme A.scheme).left).sheaf ≅ (L.pullback μ[A.scheme].left).sheaf))

attribute [local instance] Kernel.Scheme.kernelGroup

/-- Standard Weil maximal isotropy gives exactly the original full-torsion self-annihilation needed for descent. -/
theorem selfAnnihilating {H : Over (Spec (.of k))} (i : H ⟶ Kernel.Scheme.kernelObject ((𝟙 A.scheme) ^ n))
    (hlag : ∀ (T : Over (Spec (.of k))) (y : T ⟶ Kernel.Scheme.kernelObject ((𝟙 A.scheme) ^ n)),
      (∀ (U : Over (Spec (.of k))) (a : U ⟶ T) (x : U ⟶ H),
        value D ell n hn C (x ≫ i) (a ≫ y) = 1) ↔ ∃ x : T ⟶ H, x ≫ i = y) :
    NaturalPairingOrthogonal.SelfAnnihilating i
      (PairingIndependence.ReferenceTorsion.pairing (Canonical.BundledDual.canonical D) (Canonical.BundledDual.isogeny D ell).hom L hformula n) := by
  have : IsMonHom (show A.scheme ⟶ (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).withPicardGroup.abelian from
      (Canonical.BundledDual.isogeny D ell).hom) := (Canonical.BundledDual.isogeny D ell).preservesGroup
  have : IsFinite (show A.scheme ⟶ (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).withPicardGroup.abelian from
      (Canonical.BundledDual.isogeny D ell).hom).left := (Canonical.BundledDual.isogeny D ell).finite
  have : Flat (show A.scheme ⟶ (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).withPicardGroup.abelian from
      (Canonical.BundledDual.isogeny D ell).hom).left := (Canonical.BundledDual.isogeny D ell).flat
  have : Surjective (show A.scheme ⟶ (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).withPicardGroup.abelian from
      (Canonical.BundledDual.isogeny D ell).hom).left := (Canonical.BundledDual.isogeny D ell).surjective
  exact WeilCanonicalTorsionPairing.selfAnnihilating A (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D) (Canonical.BundledDual.isogeny D ell).hom n hn C
    (AbelianScheme.IsogenyQuotient.Reference.PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication (Canonical.BundledDual.canonical D)) (AbelianScheme.IsogenyQuotient.Reference.PoincareMultiplications.Construction.originalPoincareVerticalMultiplication (Canonical.BundledDual.canonical D))
    (AbelianScheme.IsogenyQuotient.Reference.PoincareInterchange.Construction.originalPoincareMultiplications_interchange (Canonical.BundledDual.canonical D))
    (Symmetry.ReferencePoincare.symmetry (Canonical.BundledDual.canonical D) (Canonical.BundledDual.isogeny D ell).hom L hformula n)
    (Symmetry.ReferencePoincare.symmetry_vertical (Canonical.BundledDual.canonical D) (Canonical.BundledDual.isogeny D ell).hom L hformula n)
    (Symmetry.ReferencePoincare.symmetry_horizontal (Canonical.BundledDual.canonical D) (Canonical.BundledDual.isogeny D ell).hom L hformula n) i hlag

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Reference.WeilPairing
