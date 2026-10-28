import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.PicardSheaf
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.QuotientDiagonal
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.IsotropicPicardImage

/-! # Picard Image -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.PicardImage.Construction

noncomputable section

/-! The original polarized isotropic quotient constructs an abelian
image in the actual homogeneous Picard sheaf. Identifying that image
with the whole sheaf remains necessary for quotient-dual representability. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {S : Scheme} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
  (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ)
  (k : Type) [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ S) (n : ℕ) (hn : 0 < n)
  {B : Over (Spec (.of k))} [GrpObj B] (f : (A.pullback s).scheme ⟶ B) [IsMonHom f]
  (hker : ∀ (T : Over (Spec (.of k))) (x : T ⟶ (A.pullback s).scheme), x ≫ f = 1 → x ^ n = 1)
  (hlag :
    let F := SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion (A.pullback s).scheme n) (Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f)
    (IsogenyQuotient.Field.PolarizationAdapter.Construction.fieldNativePolarizationPairing (A.pullback s) (D.pullback s) (pol.pullback s) n hn).relativeAnnihilator F = F)

variable [Flat f.left] [Surjective f.left]
  [IsLocallyNoetherian (B ⊗ B).left] [IsLocallyNoetherian (B ⊗ (B ⊗ B)).left]

variable [IsFinite f.left] [LocallyOfFinitePresentation f.left]
  [IsCommMonObj B] [IsProper B.hom] [Smooth B.hom] [GeometricallyIntegral B.hom]
  [IsLocallyNoetherian B.left] [IsLocallyNoetherian ((B ⊗ B) ⊗ B).left]

theorem geometricCanonicalQuotientPicard_abelian_image :
    ∃ (C : Quotients.FiniteDescent.AbelianQuotient.Construction.AbelianScheme (Spec (.of k))) (q : B ⟶ C.toOver)
      (i : uliftYoneda.{1}.obj C.toOver ⟶
        (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj),
      IsMonHom q ∧ Quotients.FiniteDescent.AbelianQuotient.Construction.FiniteLocallyFree q.left ∧ Surjective q.left ∧ Mono i ∧
        uliftYoneda.map q ≫ i = PicardSheaf.Construction.geometricCanonicalQuotientPicardSheafMap D pol k s n hn f hker hlag := by
  exact IsotropicPicardImage.Construction.nativeIsotropicQuotientPicard_abelian_image
    (Geometric.PoincareSymmetry.Construction.geometricPolarizationMap D pol k s) (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine (D.pullback s))
    (Reference.PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication (D.pullback s))
    (Reference.PoincareMultiplications.Construction.originalPoincareVerticalMultiplication (D.pullback s)) n (Geometric.PoincareSymmetry.Construction.geometricPoincareMultipleSymmetry D pol k s n)
    (Geometric.PoincareLine.Construction.geometricPoincareMultiplications_symmetry_vertical D pol k s n)
    (Reference.PoincareInterchange.Construction.originalPoincareMultiplications_interchange (D.pullback s))
    (Geometric.PoincareLine.Construction.geometricPoincareMultiplications_symmetry_horizontal D pol k s n) f hker
    (QuotientDiagonal.Construction.canonicalKernel_poincare_selfAnnihilating D pol k s n hn f hlag)
    (QuotientDiagonal.Construction.geometricCanonicalQuotientDiagonal_isAmple D pol k s n hn f hker hlag)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.PicardImage.Construction
