import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduction
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CorrespondencePointBaseChange

/-! # Reduced Model Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ReducedModelComparison.IsogenyQuotient

noncomputable section

/-! A generic model identified with a base change of the original reduction
has the same points on every reduced test scheme. No fine classification
on nonreduced tests is asserted for this model. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CorrespondencePointBaseChange

universe u
variable {B B' : Scheme.{u}} (p : B' ⟶ B) (M : Over B)

def baseChangeReductionHomEquiv (T : Over B') [IsReduced T.left] :
    (T ⟶ (Over.pullback p).obj (PELModuli.IntegralModel.Reduction.reduction M)) ≃
      (T ⟶ (Over.pullback p).obj M) := by
  letI : IsReduced (Over.mk (T.hom ≫ p)).left := ‹IsReduced T.left›
  exact (AbelianScheme.TateComparison.FieldPointTransport.pointBaseChangeEquiv p T.hom (T.hom ≫ p) rfl (PELModuli.IntegralModel.Reduction.reduction M)).trans
    ((PELModuli.IntegralModel.Reduction.reductionHomEquiv (Over.mk (T.hom ≫ p)) M).trans
      (AbelianScheme.TateComparison.FieldPointTransport.pointBaseChangeEquiv p T.hom (T.hom ≫ p) rfl M).symm)

theorem baseChangeReductionHomEquiv_apply (T : Over B') [IsReduced T.left]
    (f : T ⟶ (Over.pullback p).obj (PELModuli.IntegralModel.Reduction.reduction M)) :
    baseChangeReductionHomEquiv p M T f =
      f ≫ (Over.pullback p).map (PELModuli.IntegralModel.Reduction.reductionι M) := by
  change (AbelianScheme.TateComparison.FieldPointTransport.pointBaseChangeEquiv p T.hom (T.hom ≫ p) rfl M).symm
      ((AbelianScheme.TateComparison.FieldPointTransport.pointBaseChangeEquiv p T.hom (T.hom ≫ p) rfl (PELModuli.IntegralModel.Reduction.reduction M)) f ≫
        PELModuli.IntegralModel.Reduction.reductionι M) = _
  apply (Equiv.symm_apply_eq _).mpr
  exact (AbelianScheme.TateComparison.CorrespondencePointBaseChange.pointBaseChangeEquiv_comp p T.hom (PELModuli.IntegralModel.Reduction.reductionι M) f).symm

variable {X : Over B'} (e : X ≅ (Over.pullback p).obj (PELModuli.IntegralModel.Reduction.reduction M))

abbrev reducedModelMap : X ⟶ (Over.pullback p).obj M :=
  e.hom ≫ (Over.pullback p).map (PELModuli.IntegralModel.Reduction.reductionι M)

def reducedModelHomEquiv (T : Over B') [IsReduced T.left] :
    (T ⟶ X) ≃ (T ⟶ (Over.pullback p).obj M) :=
  (Iso.homCongr (Iso.refl T) e).trans (baseChangeReductionHomEquiv p M T)

theorem reducedModelHomEquiv_apply (T : Over B') [IsReduced T.left] (f : T ⟶ X) :
    reducedModelHomEquiv p M e T f = f ≫ reducedModelMap p M e := by
  change baseChangeReductionHomEquiv p M T ((𝟙 T ≫ f) ≫ e.hom) = _
  rw [Category.id_comp, baseChangeReductionHomEquiv_apply, Category.assoc]

theorem reducedModelMap_bijective (T : Over B') [IsReduced T.left] :
    Function.Bijective (fun f : T ⟶ X => f ≫ reducedModelMap p M e) := by
  have he : (fun f : T ⟶ X => f ≫ reducedModelMap p M e) =
      reducedModelHomEquiv p M e T := by
    funext f
    exact (reducedModelHomEquiv_apply p M e T f).symm
  rw [he]
  exact (reducedModelHomEquiv p M e T).bijective

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ReducedModelComparison.IsogenyQuotient
