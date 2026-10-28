import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.ExchangedRestriction
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberPullbackComposition
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry

/-! # External Tensor Symmetry -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.ExternalTensorSymmetry

noncomputable section

/-! The external tensor square of a line bundle has its actual diagonal-normalized exchange symmetry. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.LinePullback
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.FixedRestriction OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberPullbackComposition

variable {S : Scheme.{u}} (A : Over S) (L : Line.Bundles.LineBundle A.left)

def firstIso : (Scheme.Modules.pullback (β_ A A).hom.left).obj (Line.Fibers.fiber L (fst A A)) ≅ Line.Fibers.fiber L (snd A A) :=
  Line.Fibers.fiberPullbackIso L (β_ A A).hom (fst A A) (snd A A) (braiding_hom_fst A A)

def secondIso : (Scheme.Modules.pullback (β_ A A).hom.left).obj (Line.Fibers.fiber L (snd A A)) ≅ Line.Fibers.fiber L (fst A A) :=
  Line.Fibers.fiberPullbackIso L (β_ A A).hom (snd A A) (fst A A) (braiding_hom_snd A A)

/-- The actual factor exchange of the external tensor square. -/
def symmetry :
    (Scheme.Modules.pullback (β_ A A).hom.left).obj (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (Line.Fibers.fiber L (fst A A)) (Line.Fibers.fiber L (snd A A))) ≅
      AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (Line.Fibers.fiber L (fst A A)) (Line.Fibers.fiber L (snd A A)) :=
  Tensor.LinePullback.pullbackIso (β_ A A).hom.left _ _ (Line.Fibers.fiber_isLine L (fst A A)) (Line.Fibers.fiber_isLine L (snd A A)) ≪≫
    AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr (firstIso A L) (secondIso A L) ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCommIso _ _

/-- Restriction to the diagonal recovers the canonical identity comparison, rather than a scalar multiple. -/
theorem diagonal :
    (Scheme.Modules.pullback (AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal A).left).mapIso (symmetry A L) =
      Tensor.FixedRestriction.comparison (AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal A).left (β_ A A).hom.left
        (congrArg Over.Hom.left (AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal_swap A))
        (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (Line.Fibers.fiber L (fst A A)) (Line.Fibers.fiber L (snd A A))) := by
  let p := AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal A
  let g := (β_ A A).hom
  let e₁ := Line.Fibers.fiberPullbackIso L p (fst A A) (𝟙 A) (lift_fst _ _)
  let e₂ := Line.Fibers.fiberPullbackIso L p (snd A A) (𝟙 A) (lift_snd _ _)
  apply Tensor.ExchangedRestriction.normalized_exchange p.left g.left
    (congrArg Over.Hom.left (AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal_swap A)) _ _
    (Line.Fibers.fiber_isLine L (fst A A)) (Line.Fibers.fiber_isLine L (snd A A)) (firstIso A L) (secondIso A L) (e₁ ≪≫ e₂.symm)
  · have h := FiberPullbackComposition.fiberIso_comp L g p p (AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal_swap A) (fst A A) (snd A A) (𝟙 A)
      (braiding_hom_fst A A) (lift_snd _ _) (lift_fst _ _)
    have h' := congrArg (fun q => q ≪≫ e₂.symm) h
    simpa only [firstIso, Tensor.FixedRestriction.comparison, e₁, e₂, p, g,
      Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl] using h'
  · have h := FiberPullbackComposition.fiberIso_comp L g p p (AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal_swap A) (snd A A) (fst A A) (𝟙 A)
      (braiding_hom_snd A A) (lift_fst _ _) (lift_snd _ _)
    have h' := congrArg (fun q => q ≪≫ e₁.symm) h
    simpa only [secondIso, Tensor.FixedRestriction.comparison, e₁, e₂, p, g,
      Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl] using h'

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.ExternalTensorSymmetry
