import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.PicardClassIso
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.PoincarePullbackLine
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Polarization

/-! # Dual Poincare -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.DualPoincare.Construction

noncomputable section

/-! The original native dual map preserves the actual normalized
Poincare bundle over a Noetherian base, including its nilpotents. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization

set_option backward.isDefEq.respectTransparency false in
theorem noetherian_nativeDualMap_poincare
    {S : Scheme.{0}} [IsLocallyNoetherian S] {g h : ℕ}
    {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S}
    (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B) (f : A.scheme ⟶ B.scheme) [IsMonHom f] :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f DA DB ⊗ₘ 𝟙 A.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DA.poincare) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 DB.abelian.scheme ⊗ₘ f).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DB.poincare) := by
  have : IsLocallyNoetherian DB.abelian.scheme.left :=
    LocallyOfFiniteType.isLocallyNoetherian DB.abelian.scheme.hom
  let d := FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f DA DB
  let L := DA.poincare.pullback (d ▷ A.scheme).left
  let M := DB.poincare.pullback (DB.abelian.scheme ◁ f).left
  have hrel : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op DB.abelian.scheme) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op DB.abelian.scheme) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M) := by
    have h := Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback_poincare DA DB f (𝟙 DB.abelian.scheme)
    rw [Category.id_comp, Picard.Homomorphisms.PoincareDetection.Construction.poincareClass_id] at h
    change Picard.Homomorphisms.PoincareDetection.Construction.poincareClass DA (FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f DA DB) = _
    rw [FrobeniusKernel.Polarization.Construction.NativePicardPullback.dualMap_eq_e57]
    exact h.trans (Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullback_toRelativePicard_apply f DB.abelian.scheme
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DB.poincare))
  let eL := Isogenies.NeighborCounting.PoincareNormalization.familyPullbackZeroIso A d DA.poincare (Classical.choice DA.normalizedAtAbelianZero)
  let eM := (Relative.PoincarePullbackLine.Construction.relativePoincarePullbackLine (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DB) f).axis
  have hc : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M :=
    Quotient.sound (PicardClassIso.Construction.noetherian_bundleIso_of_relativePicard_eq A.scheme DB.abelian.scheme L M
      (Isogenies.NeighborCounting.PoincareNormalization.familyZero A DB.abelian.scheme).left (Isogenies.NeighborCounting.PoincareNormalization.familyZero_projection A DB.abelian.scheme)
      (eL ≪≫ eM.symm) hrel)
  exact hc

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.DualPoincare.Construction
