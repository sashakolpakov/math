import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.PicardCompositeSurjective
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.Source

/-! # Picard Image Source Map -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.PicardImageSourceMap.Construction

noncomputable section

/-! The canonical abelian Picard image maps to the original source
dual with the exact positive-polarization equation. This actual map is
finite, flat and surjective, without a quotient dual as input. -/

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

variable {C : Over (Spec (.of k))} [GrpObj C] (q : B ⟶ C) [IsMonHom q]
  (i : uliftYoneda.{1}.obj C ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj)
  (hfac : uliftYoneda.map q ≫ i = PicardSheaf.Construction.geometricCanonicalQuotientPicardSheafMap D pol k s n hn f hker hlag)

include hfac in
omit [GrpObj C] [IsMonHom q] in
theorem geometricCanonicalPicardImageSourceMap_factorization :
    f ≫ q ≫ PicardImage.SourceMap.Construction.picardImageSourceMap (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled (D.pullback s)) f i =
      (Geometric.PoincareSymmetry.Construction.geometricPolarizationMap D pol k s) ^ n := by
  exact PicardImage.SourceMap.Construction.picardImageSourceMap_factorization
    (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled (D.pullback s)) f i q
    (PicardSheaf.Construction.geometricCanonicalQuotientPicardSheafMap D pol k s n hn f hker hlag) hfac
    ((Geometric.PoincareSymmetry.Construction.geometricPolarizationMap D pol k s) ^ n) (Reference.PoincareMultiplications.Construction.originalPoincareVerticalMultiplication (D.pullback s))
    (IsotropicPicardCompositeSurjective.Construction.nativeIsotropicQuotientPicard_pullback (Geometric.PoincareSymmetry.Construction.geometricPolarizationMap D pol k s)
      (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine (D.pullback s))
      (Reference.PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication (D.pullback s))
      (Reference.PoincareMultiplications.Construction.originalPoincareVerticalMultiplication (D.pullback s)) n
      (Geometric.PoincareSymmetry.Construction.geometricPoincareMultipleSymmetry D pol k s n)
      (Geometric.PoincareLine.Construction.geometricPoincareMultiplications_symmetry_vertical D pol k s n)
      (Reference.PoincareInterchange.Construction.originalPoincareMultiplications_interchange (D.pullback s))
      (Geometric.PoincareLine.Construction.geometricPoincareMultiplications_symmetry_horizontal D pol k s n) f hker
      (QuotientDiagonal.Construction.canonicalKernel_poincare_selfAnnihilating D pol k s n hn f hlag))

variable [IsLocallyNoetherian ((B ⊗ B) ⊗ B).left]

include hfac in
theorem geometricCanonicalPicardImage_origin (T : Over (Spec (.of k))) :
    i.app (.op T) (ULift.up (1 : T ⟶ C)) =
      Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.trivialHomogeneousPicardClass B T := by
  have h := congrArg (fun p : uliftYoneda.{1}.obj B ⟶
    (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj => p.app (.op T) (ULift.up (1 : T ⟶ B))) hfac
  change i.app (.op T) (ULift.up ((1 : T ⟶ B) ≫ q)) =
    PicardSheaf.Construction.geometricCanonicalQuotientPicardSectionHom D pol k s n hn f hker hlag T 1 at h
  rw [MonObj.one_comp, map_one] at h
  rw [Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard.trivialHomogeneousPicardClass_eq_one]
  exact h

variable [IsCommMonObj C] [IsProper C.hom] [Smooth C.hom] [GeometricallyConnected C.hom]
  [Surjective q.left]

include hfac in
theorem geometricCanonicalPicardImageSourceMap_geometry :
    IsFinite (PicardImage.SourceMap.Construction.picardImageSourceMap (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled (D.pullback s)) f i).left ∧
      Flat (PicardImage.SourceMap.Construction.picardImageSourceMap (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled (D.pullback s)) f i).left ∧
        Surjective (PicardImage.SourceMap.Construction.picardImageSourceMap (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled (D.pullback s)) f i).left := by
  let DA := Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled (D.pullback s)
  let ell : (A.pullback s).scheme ⟶ DA.abelian := Geometric.PoincareSymmetry.Construction.geometricPolarizationMap D pol k s
  obtain ⟨hfin, _hflat, hsurj⟩ := PicardCompositeSurjective.Construction.geometricPolarizationMultiple_cover D pol k s n hn
  have : IsFinite (ell ^ n).left := hfin
  have : Surjective (ell ^ n).left := hsurj
  exact PicardImage.Source.Construction.picardImageSourceMap_finite_flat_surjective DA f q i
    (geometricCanonicalPicardImage_origin D pol k s n hn f hker hlag q i hfac) (ell ^ n)
    (geometricCanonicalPicardImageSourceMap_factorization D pol k s n hn f hker hlag q i hfac)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.PicardImageSourceMap.Construction
