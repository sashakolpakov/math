import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.BilinearProducts
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ImageAxes
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.VerticalFrame
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.IntegralConnected

/-! # Horizontal Axis Frame -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.HorizontalAxisFrame.Construction

noncomputable section

/-! Normalize the image line's second identity-axis frame to the
common zero frame supplied by its first-axis rigidification. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle

universe u
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

variable [GrpObj C] [IsMonHom q]

variable [IsCommMonObj C]
open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

local notation "Q" => OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ImageLine.Construction.rigidifiedProductPicardImageLine D βv hβv βh hβh q i hfac
local notation "L" => OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle.fromShared (OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ImageLine.Construction.normalizedProductPicardImageLine D βv hβv βh hβh q i hfac)
open OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalPullbackFrame

def picardImageHorizontalAxis : B ⟶ C ⊗ B := lift (1 : B ⟶ C) (𝟙 B)

instance picardImageHorizontalAxis_isMonHom : IsMonHom (picardImageHorizontalAxis (B := B) (C := C)) := by
  unfold picardImageHorizontalAxis
  rw [Hom.one_def]
  infer_instance

omit [IsAlgClosed k] [IsProper B.hom] [Smooth B.hom] [GeometricallyIntegral B.hom]
  [IsLocallyNoetherian B.left] [IsLocallyNoetherian (C ⊗ B).left] in
theorem picardImageHorizontalAxis_origin :
    η[B] ≫ picardImageHorizontalAxis (B := B) (C := C) = 1 := by
  rw [MonObj.one_eq_one]
  exact MonObj.one_comp _

def picardImageHorizontalFrameAtOrigin :
    (Scheme.Modules.pullback η[B].left).obj (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule B.left) ≅
      (Scheme.Modules.pullback η[B].left).obj
        ((Scheme.Modules.pullback (picardImageHorizontalAxis (B := B) (C := C)).left).obj (L).sheaf) :=
  AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso η[B].left ≪≫ RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame Q _ ≪≫
    (Picard.PoincareBundle.GlobalPullbackFrame.comparison (picardImageHorizontalAxis (B := B) (C := C)) L η[B] 1
      (picardImageHorizontalAxis_origin (B := B) (C := C))).symm

theorem existsUnique_picardImageHorizontalAxisFrame :
    ∃! e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule B.left ≅
      (Scheme.Modules.pullback (picardImageHorizontalAxis (B := B) (C := C)).left).obj (L).sheaf,
      (Scheme.Modules.pullback η[B].left).mapIso e =
        picardImageHorizontalFrameAtOrigin D βv hβv βh hβh q i hfac := by
  have : IsIso η[B].left.appTop := Poincare.ProductIsomorphisms.Construction.origin_appTop_isIso B
  exact Quotients.FiniteDescent.LineRigidificationAt.Construction.LineRigidification.existsUnique_iso η[B].left
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial B.left)
    ((ProductPicard.ImageLine.Construction.normalizedProductPicardImageLine D βv hβv βh hβh q i hfac).pullback
      (picardImageHorizontalAxis (B := B) (C := C)).left)
    (ProductPicard.ImageAxes.Construction.normalizedProductPicardImageLine_secondAxis D βv hβv βh hβh q i hfac).symm
    (picardImageHorizontalFrameAtOrigin D βv hβv βh hβh q i hfac)

def picardImageHorizontalAxisFrame : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule B.left ≅
    (Scheme.Modules.pullback (picardImageHorizontalAxis (B := B) (C := C)).left).obj (L).sheaf :=
  Classical.choose (existsUnique_picardImageHorizontalAxisFrame D βv hβv βh hβh q i hfac)

theorem picardImageHorizontalAxisFrame_origin :
    (Scheme.Modules.pullback η[B].left).mapIso (picardImageHorizontalAxisFrame D βv hβv βh hβh q i hfac) =
      picardImageHorizontalFrameAtOrigin D βv hβv βh hβh q i hfac :=
  (Classical.choose_spec (existsUnique_picardImageHorizontalAxisFrame D βv hβv βh hβh q i hfac)).1

theorem picardImageHorizontalAxisFrame_at_origin :
    Picard.PoincareBundle.GlobalPullbackFrame.atPoint (picardImageHorizontalAxis (B := B) (C := C)) L
      (picardImageHorizontalAxisFrame D βv hβv βh hβh q i hfac) η[B] 1
      (picardImageHorizontalAxis_origin (B := B) (C := C)) = RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame Q _ :=
  Poincare.VerticalFrame.Construction.atPoint_eq_of_normalized (picardImageHorizontalAxis (B := B) (C := C)) L
    (picardImageHorizontalAxisFrame D βv hβv βh hβh q i hfac) η[B] 1
    (picardImageHorizontalAxis_origin (B := B) (C := C)) (RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame Q _)
    (picardImageHorizontalAxisFrame_origin D βv hβv βh hβh q i hfac)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.HorizontalAxisFrame.Construction
