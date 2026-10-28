import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.ReindexExtension
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechReindexRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Refinement

/-! # Reindex Total -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.ReindexTotal

noncomputable section

/-! Inverse image commutes with the original relative total complexes,
their extension maps, and the refinements of their complementary covers. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {X Y : TopCat.{u}} (f : Y ⟶ X)
attribute [local instance] ReindexData.preimage_limits
variable (U : Opens X) {ι : Type u} [LinearOrder ι] (V : ι → Opens X)
  {A : Type v} [Category A] [Abelian A] [HasProducts.{u} A] [HasCoproducts.{0} A]
  (K : CochainComplex ((Opens Y)ᵒᵖ ⥤ A) ℕ)

abbrev pushed := ((OrderedCech.ReindexTotal.restriction (ReindexData.preimage f)).mapHomologicalComplex (.up ℕ)).obj K

abbrev relative := ((Refinement.restriction ((ReindexData.preimage f).obj U)).mapHomologicalComplex
  (.up ℕ)).obj K

def sourceBicomplexIso : Total.source U V (pushed f K) ≅
    Total.source ((ReindexData.preimage f).obj U) ((ReindexData.preimage f).obj ∘ V) K :=
  AugmentedOrdered.CechReindexTotal.bicomplexIso (ReindexData.preimage f) V (relative f U K)

def targetBicomplexIso : Total.target U V (pushed f K) ≅
    Total.target ((ReindexData.preimage f).obj U) ((ReindexData.preimage f).obj ∘ V) K :=
  HomologicalComplex.Hom.isoOfComponents (fun q => ReindexData.targetIso f U V (K.X q))
    (fun q q' _h => (ReindexExtension.target_naturality f U V (K.X q) (K.d q q')).symm)

def sourceTotalIso : (Total.source U V (pushed f K)).total (.up ℕ) ≅
    (Total.source ((ReindexData.preimage f).obj U) ((ReindexData.preimage f).obj ∘ V) K).total (.up ℕ) :=
  HomologicalComplex₂.total.mapIso (sourceBicomplexIso f U V K) (.up ℕ)

def targetTotalIso : (Total.target U V (pushed f K)).total (.up ℕ) ≅
    (Total.target ((ReindexData.preimage f).obj U) ((ReindexData.preimage f).obj ∘ V) K).total (.up ℕ) :=
  HomologicalComplex₂.total.mapIso (targetBicomplexIso f U V K) (.up ℕ)

omit [HasCoproducts.{0} A] in
theorem bicomplex_extension :
    Total.bicomplexMap U V (pushed f K) ≫ (targetBicomplexIso f U V K).hom =
      (sourceBicomplexIso f U V K).hom ≫
        Total.bicomplexMap ((ReindexData.preimage f).obj U) ((ReindexData.preimage f).obj ∘ V) K := by
  apply HomologicalComplex.Hom.ext
  funext q
  exact ReindexExtension.extension f U V (K.X q)

theorem total_extension :
    Total.map U V (pushed f K) ≫ (targetTotalIso f U V K).hom =
      (sourceTotalIso f U V K).hom ≫
        Total.map ((ReindexData.preimage f).obj U) ((ReindexData.preimage f).obj ∘ V) K := by
  let T := HomologicalComplex₂.totalFunctor A (.up ℕ) (.up ℕ) (.up ℕ)
  exact (T.map_comp _ _).symm.trans
    ((congrArg T.map (bicomplex_extension f U V K)).trans (T.map_comp _ _))

variable {κ : Type u} [LinearOrder κ] (W : κ → Opens X)
  (ρ : FormalCoproduct.mk κ W ⟶ FormalCoproduct.mk ι V)

theorem total_refinement :
    Refinement.map U V W ρ (pushed f K) ≫ (sourceTotalIso f U W K).hom =
      (sourceTotalIso f U V K).hom ≫
        Refinement.map ((ReindexData.preimage f).obj U) ((ReindexData.preimage f).obj ∘ V)
          ((ReindexData.preimage f).obj ∘ W) (Cech.BaseChangeRefinement.refinement (ReindexData.preimage f) V W ρ) K :=
  AugmentedOrdered.CechReindexRefinement.total_refinement (ReindexData.preimage f) V W ρ (relative f U K)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.ReindexTotal
