import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.QuotientDiagonal
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.IsotropicPicardSheaf

/-! # Picard Sheaf -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.PicardSheaf.Construction

noncomputable section

/-! The actual canonical geometric quotient maps naturally to its Picard
sheaf, before representability by a dual abelian scheme is known. -/

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

variable [IsAffineHom f.left] [Flat f.left] [Surjective f.left]
  [IsLocallyNoetherian (B ⊗ B).left] [IsLocallyNoetherian (B ⊗ (B ⊗ B)).left]

/-- The original polarization and the canonical CartierDuality self-annihilating kernel
construct the quotient map into its native homogeneous Picard sheaf. -/
def geometricCanonicalQuotientPicardSheafMap :
    uliftYoneda.{1}.obj B ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj :=
  IsotropicPicardSheaf.Construction.nativeIsotropicQuotientPicardSheafMap (Geometric.PoincareSymmetry.Construction.geometricPolarizationMap D pol k s) (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine (D.pullback s))
    (Reference.PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication (D.pullback s))
    (Reference.PoincareMultiplications.Construction.originalPoincareVerticalMultiplication (D.pullback s)) n (Geometric.PoincareSymmetry.Construction.geometricPoincareMultipleSymmetry D pol k s n)
    (Geometric.PoincareLine.Construction.geometricPoincareMultiplications_symmetry_vertical D pol k s n)
    (Reference.PoincareInterchange.Construction.originalPoincareMultiplications_interchange (D.pullback s))
    (Geometric.PoincareLine.Construction.geometricPoincareMultiplications_symmetry_horizontal D pol k s n) f hker
    (QuotientDiagonal.Construction.canonicalKernel_poincare_selfAnnihilating D pol k s n hn f hlag)

variable [IsLocallyNoetherian ((B ⊗ B) ⊗ B).left]

/-- The canonical quotient-to-Picard-sheaf map preserves the group law
on every test scheme. -/
def geometricCanonicalQuotientPicardSectionHom (T : Over (Spec (.of k))) :
    (T ⟶ B) →* (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.obj (.op T) :=
  IsotropicPicardSheaf.Construction.nativeIsotropicQuotientPicardSectionHom (Geometric.PoincareSymmetry.Construction.geometricPolarizationMap D pol k s) (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine (D.pullback s))
    (Reference.PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication (D.pullback s))
    (Reference.PoincareMultiplications.Construction.originalPoincareVerticalMultiplication (D.pullback s)) n (Geometric.PoincareSymmetry.Construction.geometricPoincareMultipleSymmetry D pol k s n)
    (Geometric.PoincareLine.Construction.geometricPoincareMultiplications_symmetry_vertical D pol k s n)
    (Reference.PoincareInterchange.Construction.originalPoincareMultiplications_interchange (D.pullback s))
    (Geometric.PoincareLine.Construction.geometricPoincareMultiplications_symmetry_horizontal D pol k s n) f hker
    (QuotientDiagonal.Construction.canonicalKernel_poincare_selfAnnihilating D pol k s n hn f hlag) T

theorem geometricCanonicalQuotientPicardSectionHom_apply
    (T : Over (Spec (.of k))) (x : T ⟶ B) :
    geometricCanonicalQuotientPicardSectionHom D pol k s n hn f hker hlag T x =
      (geometricCanonicalQuotientPicardSheafMap D pol k s n hn f hker hlag).app
        (.op T) (ULift.up x) := rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.PicardSheaf.Construction
