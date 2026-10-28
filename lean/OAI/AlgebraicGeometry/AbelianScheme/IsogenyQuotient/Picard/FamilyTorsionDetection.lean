import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledGroup
import OAI.AlgebraicGeometry.Picard.Homomorphisms.RelativeGroup
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledPoincareDetection

/-! # Family Torsion Detection -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Picard.FamilyTorsionDetection.Construction

noncomputable section

/-! An injective native Picard-family homomorphism detects torsion
from a proved tensor-power equality for its actual line bundle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.Homomorphisms.RelativeGroup.Construction

universe u
variable {S : Scheme.{u}} {B C T : Over S} [GrpObj B] [GrpObj C]

set_option backward.isDefEq.respectTransparency false in
theorem picardFamily_point_torsion
    (H : (T ⟶ C) →* (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.obj (op T))
    (hH : Function.Injective H) (x : T ⟶ C) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (T ⊗ B).left)
    (he : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard B).app (op T) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
      (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheafInclusion B).hom.app (op T) (H x))
    (n : ℕ) (hc : (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) ^ n = 1) : x ^ n = 1 := by
  let j := Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard.homogeneousPicardSheafInclusionHom B T
  have hj : Function.Injective j := by
    have hm : Mono ((Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheafInclusion B).hom.app (op T)) := inferInstance
    intro a b hab
    apply (CategoryTheory.mono_iff_injective _).mp hm
    change Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard.homogeneousPicardSheafInclusionHom B T a = Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard.homogeneousPicardSheafInclusionHom B T b at hab
    simpa only [Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard.homogeneousPicardSheafInclusionHom_apply] using hab
  apply hH
  apply hj
  rw [map_pow, map_one, map_pow, map_one]
  change (Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard.homogeneousPicardSheafInclusionHom B T (H x)) ^ n = 1
  rw [Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard.homogeneousPicardSheafInclusionHom_apply, ← he]
  have ht := congrArg (Picard.Homomorphisms.RelativeGroup.Construction.toRelativePicardHom B T) hc
  exact ((Picard.Homomorphisms.RelativeGroup.Construction.toRelativePicardHom B T).map_pow (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) n).symm.trans
    (ht.trans (Picard.Homomorphisms.RelativeGroup.Construction.toRelativePicardHom B T).map_one)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Picard.FamilyTorsionDetection.Construction
