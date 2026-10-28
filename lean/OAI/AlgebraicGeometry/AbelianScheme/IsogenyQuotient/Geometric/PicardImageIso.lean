import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RepresentedPicardImageMap
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProperMonoFinite
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.Finite
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.BaseChange
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FiberHomEquality

/-! # Picard Image Iso -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.PicardImageIso.Construction

noncomputable section

/-! A monomorphic Picard image of the correct dimension is the entire
Picard sheaf when the geometric target dual is represented. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

set_option backward.isDefEq.respectTransparency false in
theorem geometricPicardImage_isIso
    {k : Type u} [Field k] [IsAlgClosed k] {g : ℕ}
    (B Q : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
    (i : uliftYoneda.{u + 1}.obj Q.scheme ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B.scheme).obj) [Mono i] : IsIso i := by
  let m := RepresentedPicardImageMap.Construction.representedPicardImageMap (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D) i
  have : Mono m := RepresentedPicardImageMap.Construction.representedPicardImageMap_mono (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D) i
  have : Mono m.left := inferInstanceAs (Mono ((Over.forget _).map m))
  have : IsProper m.left := Picard.Homomorphisms.FiniteGroupMaps.Construction.groupHom_isProper m
  have : IsFinite m.left := ProperMonoFinite.Construction.proper_mono_finite m.left
  have : Surjective m.left := Relative.Finite.Construction.finite_geometric_abelian_hom_surjective Q D.abelian m
  have : IsClosedImmersion m.left :=
    (IsClosedImmersion.iff_isFinite_and_mono m.left).mpr ⟨inferInstance, inferInstance⟩
  have : IsReduced (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).abelian.left :=
    ArithmeticGeometry.OrdinaryLocus.Openness.SmoothReduced.Construction.isReduced_smooth_over_field (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).abelian.hom
  have : IsIso m.left := isIso_of_isClosedImmersion_of_surjective m.left
  have : IsIso ((Over.forget _).map m) := inferInstanceAs (IsIso m.left)
  have : IsIso m := isIso_of_reflects_iso m (Over.forget _)
  exact RepresentedPicardImageMap.Construction.representedPicardImageMap_isIso_sheaf (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D) i

set_option backward.isDefEq.respectTransparency false in
theorem geometricBaseChangePicardImage_isIso
    {S : Scheme.{u}} {g : ℕ} (B Q : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (i : uliftYoneda.{u + 1}.obj Q.scheme ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B.scheme).obj) [Mono i]
    {k : Type u} [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ S)
    (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData (B.pullback s)) : IsIso (PicardImage.BaseChange.Construction.picardImageBaseChangeMap i s) := by
  have : Mono (PicardImage.BaseChange.Construction.picardImageBaseChangeMap i s) := PicardImage.BaseChange.Construction.picardImageBaseChangeMap_mono i s
  exact geometricPicardImage_isIso (B.pullback s) (Q.pullback s) D (PicardImage.BaseChange.Construction.picardImageBaseChangeMap i s)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.PicardImageIso.Construction
