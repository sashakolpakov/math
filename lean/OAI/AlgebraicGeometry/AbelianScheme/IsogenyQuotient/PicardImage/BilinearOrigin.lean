import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.BilinearProducts
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.NormalizedProductOrigin

/-! # Bilinear Origin -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.BilinearOrigin.Construction

noncomputable section

/-! Canonical fiber comparisons identify the origin of each normalized
image product with multiplication in the common zero frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle

universe u
section Generic
variable {k : Type u} [Field k] {A C : Over (Spec (.of k))} [GrpObj A] [GrpObj C]
  (Q : FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine A C) {T : Over (Spec (.of k))} [GrpObj T]

theorem rigidifiedPointOriginFrame_comparison (x : T ⟶ C) (a : T ⟶ A)
    [IsMonHom x] [IsMonHom a] (h : η[T] ≫ lift x a = 1) :
    RigidifiedPointFrames.Construction.rigidifiedPointOriginFrame Q x a ≪≫
      Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared Q.bundle) η[T] (lift x a) 1 h = RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame Q _ := by
  unfold RigidifiedPointFrames.Construction.rigidifiedPointOriginFrame
  rw [FiberProductOrigin.Construction.fiberPullbackIso_eq_comparison]
  change (RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame Q _ ≪≫
    (Picard.PoincareBundle.GlobalPullbackFrame.comparison (lift x a) (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared Q.bundle) η[T] 1 h).symm) ≪≫
    Picard.PoincareBundle.GlobalPullbackFrame.comparison (lift x a) (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared Q.bundle) η[T] 1 h = _
  simp only [Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]
end Generic

variable {k : Type u} [Field k] [IsAlgClosed k]
  {B : Over (Spec (.of k))} [GrpObj B] [IsCommMonObj B]
  [IsProper B.hom] [Smooth B.hom] [GeometricallyIntegral B.hom]
  [IsLocallyNoetherian B.left]
  (D : FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine B B)
  (βv : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Vertical.ProductParameters.inputLeft B B))
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Vertical.ProductParameters.inputRight B B))
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Vertical.ProductParameters.outputPoint B B)))
  (hβv : IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom βv))
  (βh : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Product.ParameterSchemes.inputLeft B B))
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Product.ParameterSchemes.inputRight B B))
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Product.ParameterSchemes.outputPoint B B)))
  (hβh : IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom βh))

variable {C : Over (Spec (.of k))} (q : B ⟶ C)
  (i : uliftYoneda.{u + 1}.obj C ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj)
  (hfac : uliftYoneda.map q ≫ i = ProductPicard.SheafMap.Construction.productNativePicardSheafMap (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) βv hβv)

variable [IsAffineHom (q ⊗ₘ 𝟙 B).left] [Flat (q ⊗ₘ 𝟙 B).left]
  [Surjective (q ⊗ₘ 𝟙 B).left] [IsLocallyNoetherian (C ⊗ B).left]
  [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left]

variable [GrpObj C] [IsMonHom q]

variable [IsCommMonObj C]
  {T : Over (Spec (.of k))} [GrpObj T] [IsLocallyNoetherian T.left]
  [Smooth T.hom] [IsProper T.hom] [GeometricallyConnected T.hom]

attribute [local instance] NormalizedPointProducts.Construction.imagePointMapMul_isMonHom

local notation "Q" => OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ImageLine.Construction.rigidifiedProductPicardImageLine D βv hβv βh hβh q i hfac
local notation "L" => OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle.fromShared (OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ImageLine.Construction.normalizedProductPicardImageLine D βv hβv βh hβh q i hfac)

theorem normalizedPicardImageBilinearLeft_at_origin
    (x y : T ⟶ C) (a : T ⟶ B) [IsMonHom x] [IsMonHom y] [IsMonHom a] :
    Picard.PoincareBundle.Line.Fibers.pullBilinear L η[T] (lift x a) (lift y a) (lift (x * y) a) 1 1 1
      (NormalizedProductOrigin.Construction.groupMap_origin (lift x a)) (NormalizedProductOrigin.Construction.groupMap_origin (lift y a)) (NormalizedProductOrigin.Construction.groupMap_origin (lift (x * y) a))
      (BilinearProducts.Construction.normalizedPicardImageBilinearLeft D βv hβv βh hβh q i hfac x y a) =
        Poincare.BilinearProducts.Construction.framedLineProduct (RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame Q _) (RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame Q _)
          (RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame Q _) :=
  FiberProductOrigin.Construction.pullBilinear_of_framed_pullback L η[T] (lift x a) (lift y a) (lift (x * y) a) 1 1 1
    (NormalizedProductOrigin.Construction.groupMap_origin (lift x a)) (NormalizedProductOrigin.Construction.groupMap_origin (lift y a)) (NormalizedProductOrigin.Construction.groupMap_origin (lift (x * y) a))
    (BilinearProducts.Construction.normalizedPicardImageBilinearLeft D βv hβv βh hβh q i hfac x y a)
    (NormalizedPointProducts.Construction.picardImagePointOriginFrame D βv hβv βh hβh q i hfac x a)
    (NormalizedPointProducts.Construction.picardImagePointOriginFrame D βv hβv βh hβh q i hfac y a)
    (NormalizedPointProducts.Construction.picardImagePointOriginFrame D βv hβv βh hβh q i hfac (x * y) a)
    (RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame Q _) (RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame Q _) (RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame Q _)
    (rigidifiedPointOriginFrame_comparison Q x a _) (rigidifiedPointOriginFrame_comparison Q y a _)
    (rigidifiedPointOriginFrame_comparison Q (x * y) a _)
    (BilinearProducts.Construction.normalizedPicardImageBilinearLeft_origin D βv hβv βh hβh q i hfac x y a)

omit [IsMonHom q] in
theorem normalizedPicardImageBilinearRight_at_origin
    (x : T ⟶ C) (a b : T ⟶ B) [IsMonHom x] [IsMonHom a] [IsMonHom b] :
    Picard.PoincareBundle.Line.Fibers.pullBilinear L η[T] (lift x a) (lift x b) (lift x (a * b)) 1 1 1
      (NormalizedProductOrigin.Construction.groupMap_origin (lift x a)) (NormalizedProductOrigin.Construction.groupMap_origin (lift x b)) (NormalizedProductOrigin.Construction.groupMap_origin (lift x (a * b)))
      (BilinearProducts.Construction.normalizedPicardImageBilinearRight D βv hβv βh hβh q i hfac x a b) =
        Poincare.BilinearProducts.Construction.framedLineProduct (RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame Q _) (RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame Q _)
          (RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame Q _) :=
  FiberProductOrigin.Construction.pullBilinear_of_framed_pullback L η[T] (lift x a) (lift x b) (lift x (a * b)) 1 1 1
    (NormalizedProductOrigin.Construction.groupMap_origin (lift x a)) (NormalizedProductOrigin.Construction.groupMap_origin (lift x b)) (NormalizedProductOrigin.Construction.groupMap_origin (lift x (a * b)))
    (BilinearProducts.Construction.normalizedPicardImageBilinearRight D βv hβv βh hβh q i hfac x a b)
    (NormalizedPointProducts.Construction.picardImagePointOriginFrame D βv hβv βh hβh q i hfac x a)
    (NormalizedPointProducts.Construction.picardImagePointOriginFrame D βv hβv βh hβh q i hfac x b)
    (NormalizedPointProducts.Construction.picardImagePointOriginFrame D βv hβv βh hβh q i hfac x (a * b))
    (RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame Q _) (RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame Q _) (RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame Q _)
    (rigidifiedPointOriginFrame_comparison Q x a _) (rigidifiedPointOriginFrame_comparison Q x b _)
    (rigidifiedPointOriginFrame_comparison Q x (a * b) _)
    (BilinearProducts.Construction.normalizedPicardImageBilinearRight_origin D βv hβv βh hβh q i hfac x a b)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.BilinearOrigin.Construction
