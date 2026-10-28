import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.PicardSheaf
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.IsotropicPicardCompositeSurjective
import OAI.AlgebraicGeometry.Picard.PoincareBundle.PositiveMultiple

/-! # Picard Composite Surjective -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.PicardCompositeSurjective.Construction

noncomputable section

/-! The canonical quotient Picard map is locally surjective after
pullback to the original source Picard sheaf. The source polarization
supplies the actual positive-multiple fppf cover, with no quotient dual. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames

variable {S : Scheme} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
  (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ)
  (k : Type) [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ S) (n : ℕ) (hn : 0 < n)
  {B : Over (Spec (.of k))} [GrpObj B] (f : (A.pullback s).scheme ⟶ B) [IsMonHom f]
  (hker : ∀ (T : Over (Spec (.of k))) (x : T ⟶ (A.pullback s).scheme), x ≫ f = 1 → x ^ n = 1)
  (hlag :
    let F := SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion (A.pullback s).scheme n) (Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f)
    (IsogenyQuotient.Field.PolarizationAdapter.Construction.fieldNativePolarizationPairing (A.pullback s) (D.pullback s) (pol.pullback s) n hn).relativeAnnihilator F = F)

variable [IsAffineHom f.left] [Flat f.left] [Surjective f.left]
  [IsLocallyNoetherian (B ⊗ B).left] [IsLocallyNoetherian (B ⊗ (B ⊗ B)).left]

include hn in
omit [IsAlgClosed k] in
theorem geometricPolarizationMultiple_cover :
    IsFinite ((Geometric.PoincareSymmetry.Construction.geometricPolarizationMap D pol k s) ^ n).left ∧
      Flat ((Geometric.PoincareSymmetry.Construction.geometricPolarizationMap D pol k s) ^ n).left ∧
        Surjective ((Geometric.PoincareSymmetry.Construction.geometricPolarizationMap D pol k s) ^ n).left := by
  let DA := Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled (D.pullback s)
  let ell : (A.pullback s).scheme ⟶ DA.abelian := Geometric.PoincareSymmetry.Construction.geometricPolarizationMap D pol k s
  have : IsMonHom ell := (pol.isogeny.pullback s).preservesGroup
  have : IsFinite ell.left := (pol.isogeny.pullback s).finite
  have : Flat ell.left := (pol.isogeny.pullback s).flat
  have : Surjective ell.left := (pol.isogeny.pullback s).surjective
  exact Picard.PoincareBundle.PositiveMultiple.positive_multiple_cover DA ell n hn

include hn in
theorem geometricPoincareVerticalPicard_locallySurjective :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over (Spec (.of k)))
      (Poincare.VerticalPicardSheafMap.Construction.poincareVerticalPicardSheafMap ((Geometric.PoincareSymmetry.Construction.geometricPolarizationMap D pol k s) ^ n)
        (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine (D.pullback s)) (Reference.PoincareMultiplications.Construction.originalPoincareVerticalMultiplication (D.pullback s))) := by
  let DA := Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled (D.pullback s)
  let ell : (A.pullback s).scheme ⟶ DA.abelian := Geometric.PoincareSymmetry.Construction.geometricPolarizationMap D pol k s
  obtain ⟨hfin, hflat, hsurj⟩ := geometricPolarizationMultiple_cover D pol k s n hn
  have : IsFinite (ell ^ n).left := hfin
  have : Flat (ell ^ n).left := hflat
  have : Surjective (ell ^ n).left := hsurj
  have : IsLocallyNoetherian DA.abelian.left := LocallyOfFiniteType.isLocallyNoetherian DA.abelian.hom
  exact Poincare.VerticalPicardSheafMap.Construction.poincareVerticalPicardSheafMap_locallySurjective DA (ell ^ n)
    (Reference.PoincareMultiplications.Construction.originalPoincareVerticalMultiplication (D.pullback s))

theorem geometricCanonicalQuotientPicard_pullback_locallySurjective :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over (Spec (.of k)))
      (PicardSheaf.Construction.geometricCanonicalQuotientPicardSheafMap D pol k s n hn f hker hlag ≫
        (Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullback (A.pullback s).scheme B f).hom) := by
  exact IsotropicPicardCompositeSurjective.Construction.nativeIsotropicQuotientPicard_pullback_locallySurjective
    (Geometric.PoincareSymmetry.Construction.geometricPolarizationMap D pol k s) (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine (D.pullback s))
    (Reference.PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication (D.pullback s))
    (Reference.PoincareMultiplications.Construction.originalPoincareVerticalMultiplication (D.pullback s)) n
    (Geometric.PoincareSymmetry.Construction.geometricPoincareMultipleSymmetry D pol k s n)
    (Geometric.PoincareLine.Construction.geometricPoincareMultiplications_symmetry_vertical D pol k s n)
    (Reference.PoincareInterchange.Construction.originalPoincareMultiplications_interchange (D.pullback s))
    (Geometric.PoincareLine.Construction.geometricPoincareMultiplications_symmetry_horizontal D pol k s n) f hker
    (QuotientDiagonal.Construction.canonicalKernel_poincare_selfAnnihilating D pol k s n hn f hlag)
    (geometricPoincareVerticalPicard_locallySurjective D pol k s n hn)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.PicardCompositeSurjective.Construction
