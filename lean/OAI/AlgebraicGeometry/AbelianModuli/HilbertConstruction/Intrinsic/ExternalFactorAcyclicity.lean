import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PushforwardAcyclicCover
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.SheafComplex
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.LineBundles
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.FrameCover

/-! # External Factor Acyclicity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.ExternalFactorAcyclicity

noncomputable section

/-! Native open factors of an external line bundle are acyclic on the same proper-factor inverse-image cover when the parameter open is affine. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.AlgebraicGeometry Opposite
universe u

variable {S X Y P : Scheme.{u}} [IsAffine S] [Y.IsSeparated] [P.IsSeparated]
variable {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
variable (H : IsPullback a b f g) (L : Line.Bundles.LineBundle X) (N : Line.Bundles.LineBundle Y)

include H in
theorem nativeExternalFactor_commonCover_acyclic
    (U : Y.Opens) (hU : IsAffineOpen U)
    {ι : Type u} (V : ι → X.Opens) (ha : ∀ i, IsAffineOpen (V i)) :
    Cech.AcyclicIntersectionColumns.IntrinsicCech.CechIntersectionsAcyclic (fun i => a ⁻¹ᵁ V i)
      ((IntrinsicCech.SheafComplex.cechFactorPresheaf (UnderlyingAdditiveSheafExactness.ModuleSheaf.sheaf (((L.pullback a).tensor (N.pullback b)).sheaf))).obj
        (op (b ⁻¹ᵁ U))) := by
  let d := (b ⁻¹ᵁ U).ι
  let E := (L.pullback a).tensor (N.pullback b)
  have : E.sheaf.IsQuasicoherent := E.isQuasicoherent
  have : IsAffine U.toScheme := hU
  have : IsAffineHom U.ι := Affine.FrameCover.affine_source_morphism_affine U.ι
  have : IsAffineHom d :=
    isAffineHom_isStableUnderBaseChange.of_isPullback (isPullback_morphismRestrict b U) inferInstance
  have hlocal : IsPullback (d ≫ a) (b ∣_ U) f (U.ι ≫ g) :=
    (isPullback_morphismRestrict b U).flip.paste_horiz H
  have : IsAffineHom (d ≫ a) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback hlocal.flip inferInstance
  change Cech.AcyclicIntersectionColumns.IntrinsicCech.CechIntersectionsAcyclic (fun i => a ⁻¹ᵁ V i)
    ((SheafOfModules.toSheaf P.ringCatSheaf).obj ((Scheme.Modules.pushforward d).obj (E.sheaf.restrict d)))
  exact Affine.PushforwardAcyclicCover.affinePushforward_inverseImage_cover_acyclic d (E.sheaf.restrict d) a V ha

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.ExternalFactorAcyclicity
