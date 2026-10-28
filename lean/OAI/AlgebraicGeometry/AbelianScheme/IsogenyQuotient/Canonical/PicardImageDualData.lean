import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.PicardImageSourceMap
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.IsotropicPicardDual
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AbelianGeometric
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.Noetherian
import OAI.AlgebraicGeometry.Picard.PoincareBundle.TypedKernelAnnihilator

/-! # Picard Image Dual Data -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.PicardImageDualData.Construction

noncomputable section

section

/-! The original polarization and its full canonical self-annihilating
quotient kernel make the constructed Picard image the entire quotient dual. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames

variable {S : Scheme} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
  (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ)
  (k : Type) [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ S) (n : ℕ) (hn : 0 < n)
  {B : Over (Spec (.of k))} [GrpObj B] (f : (A.pullback s).scheme ⟶ B) [IsMonHom f]
  (hker : ∀ (T : Over (Spec (.of k))) (x : T ⟶ (A.pullback s).scheme), x ≫ f = 1 → x ^ n = 1)
  (hlag :
    let F := SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion (A.pullback s).scheme n) (Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f)
    (IsogenyQuotient.Field.PolarizationAdapter.Construction.fieldNativePolarizationPairing (A.pullback s) (D.pullback s) (pol.pullback s) n hn).relativeAnnihilator F = F)

variable [IsFinite f.left] [Flat f.left] [Surjective f.left]
  [IsLocallyNoetherian (B ⊗ B).left] [IsLocallyNoetherian (B ⊗ (B ⊗ B)).left]

variable {C : Over (Spec (.of k))} [GrpObj C] (q : B ⟶ C) [IsMonHom q]
  (i : uliftYoneda.{1}.obj C ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj)
  (hfac : uliftYoneda.map q ≫ i = PicardSheaf.Construction.geometricCanonicalQuotientPicardSheafMap D pol k s n hn f hker hlag)

variable [IsLocallyNoetherian ((B ⊗ B) ⊗ B).left]
  [LocallyOfFinitePresentation f.left]
  [IsCommMonObj B] [IsProper B.hom] [Smooth B.hom] [GeometricallyConnected B.hom]
  [IsCommMonObj C] [IsProper C.hom] [Smooth C.hom] [GeometricallyConnected C.hom]
  [IsFinite q.left] [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left]
  [Mono i]

attribute [local instance] Picard.PoincareBundle.Product.Covers.tensorAffine Picard.PoincareBundle.Product.Covers.tensorFlat Picard.PoincareBundle.Product.Covers.tensorSurjective

include hfac in
set_option backward.isDefEq.respectTransparency false in
theorem geometricCanonicalPicardImage_isIso (hc : Nat.Coprime n ((∏ j, δ j) ^ 2)) : IsIso i := by
  let DA := Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled (D.pullback s)
  let ell : (A.pullback s).scheme ⟶ DA.abelian := Geometric.PoincareSymmetry.Construction.geometricPolarizationMap D pol k s
  have : IsMonHom ell := (pol.isogeny.pullback s).preservesGroup
  have : GeometricallyIntegral (A.pullback s).scheme.hom :=
    Quotients.FiniteDescent.AbelianGeometric.Construction.AbelianGeometricIntegral.geometricallyIntegral (A.pullback s).scheme
  have : GeometricallyIntegral B.hom := Quotients.FiniteDescent.AbelianGeometric.Construction.AbelianGeometricIntegral.geometricallyIntegral B
  have : IsLocallyNoetherian B.left := LocallyOfFiniteType.isLocallyNoetherian B.hom
  have : IsLocallyNoetherian DA.abelian.left := LocallyOfFiniteType.isLocallyNoetherian DA.abelian.hom
  have : IsLocallyNoetherian (C ⊗ B).left := Picard.PoincareBundle.Product.Noetherian.product_noetherian C B
  let sourceMap := PicardImage.SourceMap.Construction.picardImageSourceMap DA f i
  have : IsMonHom sourceMap := PicardImage.SourceMap.Construction.picardImageSourceMap_isMonHom DA f i
    (PicardImageSourceMap.Construction.geometricCanonicalPicardImage_origin D pol k s n hn f hker hlag q i hfac)
  have hs := PicardImageSourceMap.Construction.geometricCanonicalPicardImageSourceMap_geometry D pol k s n hn f hker hlag q i hfac
  have : IsFinite sourceMap.left := hs.1
  have : Flat sourceMap.left := hs.2.1
  have : Surjective sourceMap.left := hs.2.2
  have : LocallyOfFinitePresentation sourceMap.left := inferInstance
  exact Intrinsic.IsotropicPicardDual.Construction.nativeIsotropicPicardImage_isIso DA ell (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine (D.pullback s))
    (Reference.PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication (D.pullback s))
    (Reference.PoincareMultiplications.Construction.originalPoincareVerticalMultiplication (D.pullback s)) n
    (Geometric.PoincareSymmetry.Construction.geometricPoincareMultipleSymmetry D pol k s n)
    (Geometric.PoincareLine.Construction.geometricPoincareMultiplications_symmetry_vertical D pol k s n)
    (Reference.PoincareInterchange.Construction.originalPoincareMultiplications_interchange (D.pullback s))
    (Geometric.PoincareLine.Construction.geometricPoincareMultiplications_symmetry_horizontal D pol k s n) f hker
    (QuotientDiagonal.Construction.canonicalKernel_poincare_selfAnnihilating D pol k s n hn f hlag) q i hfac
    ((∏ j, δ j) ^ 2) hc
    (PicardImageSourceMap.Construction.geometricCanonicalPicardImageSourceMap_factorization D pol k s n hn f hker hlag q i hfac)
    (Picard.PoincareBundle.TypedKernelAnnihilator.killed_by_type_degree (pol.isogeny.pullback s) δ (pol.pullback s).kernelType)
    (Geometric.CanonicalPoincarePairing.Construction.geometricPoincarePairing_isPerfect_of_coprime D pol k s n hn hc)

end

/-! The canonical isotropic quotient has full dual data, with the actual
Picard image as its abelian scheme and its descended line as the Poincare bundle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames

variable {S : Scheme} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
  (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ)
  (k : Type) [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ S) (n : ℕ) (hn : 0 < n)
  {B : Over (Spec (.of k))} [GrpObj B] (f : (A.pullback s).scheme ⟶ B) [IsMonHom f]
  (hker : ∀ (T : Over (Spec (.of k))) (x : T ⟶ (A.pullback s).scheme), x ≫ f = 1 → x ^ n = 1)
  (hlag :
    let F := SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion (A.pullback s).scheme n) (Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f)
    (IsogenyQuotient.Field.PolarizationAdapter.Construction.fieldNativePolarizationPairing (A.pullback s) (D.pullback s) (pol.pullback s) n hn).relativeAnnihilator F = F)

variable [IsFinite f.left] [Flat f.left] [Surjective f.left]
  [IsLocallyNoetherian (B ⊗ B).left] [IsLocallyNoetherian (B ⊗ (B ⊗ B)).left]

variable {C : Over (Spec (.of k))} [GrpObj C] (q : B ⟶ C) [IsMonHom q]
  (i : uliftYoneda.{1}.obj C ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj)
  (hfac : uliftYoneda.map q ≫ i = PicardSheaf.Construction.geometricCanonicalQuotientPicardSheafMap D pol k s n hn f hker hlag)

variable [IsLocallyNoetherian ((B ⊗ B) ⊗ B).left]
  [LocallyOfFinitePresentation f.left]
  [IsCommMonObj B] [IsProper B.hom] [Smooth B.hom] [GeometricallyConnected B.hom]
  [IsCommMonObj C] [IsProper C.hom] [Smooth C.hom] [GeometricallyConnected C.hom]
  [IsFinite q.left] [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left]
  [Mono i]

attribute [local instance] Picard.PoincareBundle.Product.Covers.tensorAffine Picard.PoincareBundle.Product.Covers.tensorFlat Picard.PoincareBundle.Product.Covers.tensorSurjective

include hfac in
set_option backward.isDefEq.respectTransparency false in
def geometricCanonicalPicardImageDualData (hc : Nat.Coprime n ((∏ j, δ j) ^ 2)) :
    Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B := by
  let DA := Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled (D.pullback s)
  let ell : (A.pullback s).scheme ⟶ DA.abelian := Geometric.PoincareSymmetry.Construction.geometricPolarizationMap D pol k s
  have : IsMonHom ell := (pol.isogeny.pullback s).preservesGroup
  have : GeometricallyIntegral (A.pullback s).scheme.hom :=
    Quotients.FiniteDescent.AbelianGeometric.Construction.AbelianGeometricIntegral.geometricallyIntegral (A.pullback s).scheme
  have : GeometricallyIntegral B.hom := Quotients.FiniteDescent.AbelianGeometric.Construction.AbelianGeometricIntegral.geometricallyIntegral B
  have : IsLocallyNoetherian B.left := LocallyOfFiniteType.isLocallyNoetherian B.hom
  have : IsLocallyNoetherian DA.abelian.left := LocallyOfFiniteType.isLocallyNoetherian DA.abelian.hom
  have : IsLocallyNoetherian (C ⊗ B).left := Picard.PoincareBundle.Product.Noetherian.product_noetherian C B
  let sourceMap := PicardImage.SourceMap.Construction.picardImageSourceMap DA f i
  have : IsMonHom sourceMap := PicardImage.SourceMap.Construction.picardImageSourceMap_isMonHom DA f i
    (PicardImageSourceMap.Construction.geometricCanonicalPicardImage_origin D pol k s n hn f hker hlag q i hfac)
  have hs := PicardImageSourceMap.Construction.geometricCanonicalPicardImageSourceMap_geometry D pol k s n hn f hker hlag q i hfac
  have : IsFinite sourceMap.left := hs.1
  have : Flat sourceMap.left := hs.2.1
  have : Surjective sourceMap.left := hs.2.2
  have : LocallyOfFinitePresentation sourceMap.left := inferInstance
  exact Intrinsic.IsotropicPicardDual.Construction.nativeIsotropicPicardImageDualData DA ell (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine (D.pullback s))
    (Reference.PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication (D.pullback s))
    (Reference.PoincareMultiplications.Construction.originalPoincareVerticalMultiplication (D.pullback s)) n
    (Geometric.PoincareSymmetry.Construction.geometricPoincareMultipleSymmetry D pol k s n)
    (Geometric.PoincareLine.Construction.geometricPoincareMultiplications_symmetry_vertical D pol k s n)
    (Reference.PoincareInterchange.Construction.originalPoincareMultiplications_interchange (D.pullback s))
    (Geometric.PoincareLine.Construction.geometricPoincareMultiplications_symmetry_horizontal D pol k s n) f hker
    (QuotientDiagonal.Construction.canonicalKernel_poincare_selfAnnihilating D pol k s n hn f hlag) q i hfac
    ((∏ j, δ j) ^ 2) hc
    (PicardImageSourceMap.Construction.geometricCanonicalPicardImageSourceMap_factorization D pol k s n hn f hker hlag q i hfac)
    (Picard.PoincareBundle.TypedKernelAnnihilator.killed_by_type_degree (pol.isogeny.pullback s) δ (pol.pullback s).kernelType)
    (Geometric.CanonicalPoincarePairing.Construction.geometricPoincarePairing_isPerfect_of_coprime D pol k s n hn hc)

theorem geometricCanonicalPicardImageDualData_abelian
    (hc : Nat.Coprime n ((∏ j, δ j) ^ 2)) :
    (geometricCanonicalPicardImageDualData D pol k s n hn f hker hlag q i hfac hc).abelian = C := rfl

theorem geometricCanonicalPicardImageDualData_value
    (hc : Nat.Coprime n ((∏ j, δ j) ^ 2)) (T : Over (Spec (.of k))) (x : T ⟶ C) :
    (geometricCanonicalPicardImageDualData D pol k s n hn f hker hlag q i hfac hc).representable.homEquiv x =
      i.app (.op T) (ULift.up x) := rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.PicardImageDualData.Construction
