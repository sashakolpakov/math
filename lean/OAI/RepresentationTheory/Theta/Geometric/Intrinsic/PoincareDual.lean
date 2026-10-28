import OAI.AlgebraicGeometry.Picard.Homomorphisms.DualPullback
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.NormalizedPicardInjection
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PEL
import OAI.AlgebraicGeometry.Albanese.Construction.Rigidity

/-! # Poincare Dual -/

namespace OAI.RepresentationTheory.Theta.Geometric.Intrinsic.PoincareDual

noncomputable section

/-! The represented Picard pullback is an actual Poincare dual for the
original group structure, with equality of the algebraic line classes. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.Homomorphisms.DualPullback.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization

variable {k : Type} [Field k] [IsAlgClosed k] {g h : ℕ}
    {A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} {B : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h (Spec (.of k))}
    (DA : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
    (f : A.scheme ⟶ B.scheme) [IsMonHom f]

theorem nativePoincareDual_pullback_class :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 DB.abelian.scheme ⊗ₘ f).left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DB.poincare) =
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (AlgebraicGeometry.Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback DA DB f ⊗ₘ 𝟙 A.scheme).left
        (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DA.poincare) := by
  let : CompactSpace DB.abelian.scheme.left :=
    QuasiCompact.compactSpace_of_compactSpace DB.abelian.scheme.hom
  let : QuasiSeparatedSpace DB.abelian.scheme.left :=
    quasiSeparatedSpace_of_quasiSeparated DB.abelian.scheme.hom
  let d := AlgebraicGeometry.Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback DA DB f
  let L := DB.poincare.pullback (DB.abelian.scheme ◁ f).left
  let M := DA.poincare.pullback (d ▷ A.scheme).left
  have he : (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op DB.abelian.scheme) (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M) =
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op DB.abelian.scheme) (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) := by
    have hp := AlgebraicGeometry.Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback_poincare DA DB f (𝟙 DB.abelian.scheme)
    rw [Category.id_comp, AlgebraicGeometry.Picard.Homomorphisms.PoincareDetection.Construction.poincareClass_id] at hp
    exact hp.trans (AlgebraicGeometry.Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullback_toRelativePicard_apply f DB.abelian.scheme
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DB.poincare))
  have hc := AlgebraicGeometry.PELModuli.IntegralModel.NormalizedPicardInjection.NormalizedPicard.class_eq_of_picard_eq A L M
    (AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization.abelianGlobalZeroIso DB f)
    (AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization.familyPullbackZeroIso A d DA.poincare DA.normalizedAtAbelianZero.some) he.symm
  change AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (DB.abelian.scheme ◁ f).left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DB.poincare) =
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (AlgebraicGeometry.Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback DA DB f ▷ A.scheme).left
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DA.poincare) at hc
  simpa only [id_tensorHom, tensorHom_id] using hc

theorem nativePoincareDual_isMonHom [IsIntegral (DB.abelian.scheme ⊗ DB.abelian.scheme).left] :
    IsMonHom (AlgebraicGeometry.Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback DA DB f) := by
  apply AlgebraicGeometry.Albanese.Construction.Rigidity.isMonHom_of_pointed_of_integral_product DB.abelian.scheme DA.abelian.scheme
  simpa only [MonObj.one_eq_one] using AlgebraicGeometry.Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback_one DA DB f (𝟙_ _)

theorem exists_nativePoincareDual_end {R : Type} [CommRing R] {level : ℕ}
    (D : AlgebraicGeometry.AbelianScheme.TateComparison.PEL.PELFamilyData R g level (Spec (.of k)))
    [IsIntegral (D.dual.abelian.scheme ⊗ D.dual.abelian.scheme).left]
    (a : AlgebraicGeometry.AbelianScheme.TateComparison.End.IntegralEnd D.abelian.scheme) :
    ∃ d : AlgebraicGeometry.AbelianScheme.TateComparison.End.IntegralEnd D.dual.abelian.scheme, D.IsPoincareDual a d := by
  let f := AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap D.abelian.scheme a
  let d := AlgebraicGeometry.Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback D.dual D.dual f
  let : IsMonHom d := nativePoincareDual_isMonHom D.dual D.dual f
  refine ⟨AlgebraicGeometry.AbelianScheme.TateComparison.End.endOfSchemeMap D.dual.abelian.scheme d, ?_⟩
  unfold AlgebraicGeometry.AbelianScheme.TateComparison.PEL.PELFamilyData.IsPoincareDual
  rw [AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap_ofSchemeMap]
  exact nativePoincareDual_pullback_class D.dual D.dual f

end

end OAI.RepresentationTheory.Theta.Geometric.Intrinsic.PoincareDual
