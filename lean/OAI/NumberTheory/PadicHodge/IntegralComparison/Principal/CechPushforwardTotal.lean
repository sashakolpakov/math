import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CechPushforwardCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.ReindexTotal

/-! # Cech Pushforward Total -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CechPushforwardTotal.Coordinates

noncomputable section

/-! The principal-to-relative coordinate square for the actual total
complexes and their homology under inverse image of opens. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex
open OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.ReindexTotal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {X Y : TopCat.{u}} (f : Y ⟶ X)
  {C : Type u} [Preorder C] [HasFiniteProducts C] (F : C ⥤ Opens X)
  {ι : Type u} [LinearOrder ι] (W : ι → C)
  [∀ (n : ℕ) (a : Fin (n+1) → ι), PreservesLimit (Discrete.functor (W ∘ a)) F]
  {A : Type v} [Category A] [Abelian A] [HasProducts.{u} A] [HasCoproducts.{0} A]
  (K : CochainComplex ((Opens Y)ᵒᵖ ⥤ A) ℕ)
attribute [local instance] RelativeCech.ReindexData.preimage_limits CechPushforwardCoordinates.pulled_products

omit [HasCoproducts A] in
theorem bicomplex :
    (AugmentedCech.AmbientTotal.bicomplexIso F W (RelativeCech.ReindexTotal.pushed f K)).hom ≫
      (RelativeCech.ReindexTotal.sourceBicomplexIso f (F.obj (⊤_ C)) (F.obj ∘ W) K).hom =
    (AugmentedCech.AmbientTotal.bicomplexIso (CechPushforwardCoordinates.pulled f F) W K).hom := by
  apply HomologicalComplex.Hom.ext
  funext q
  exact CechPushforwardCoordinates.ambient f F W (K.X q)

theorem total :
    (AugmentedCech.AmbientTotal.totalIso F W (RelativeCech.ReindexTotal.pushed f K)).hom ≫
      (RelativeCech.ReindexTotal.sourceTotalIso f (F.obj (⊤_ C)) (F.obj ∘ W) K).hom =
    (AugmentedCech.AmbientTotal.totalIso (CechPushforwardCoordinates.pulled f F) W K).hom := by
  let T := HomologicalComplex₂.totalFunctor A (.up ℕ) (.up ℕ) (.up ℕ)
  exact (T.map_comp _ _).symm.trans (congrArg T.map (bicomplex f F W K))

theorem homology (q : ℕ) :
    homologyMap (AugmentedCech.AmbientTotal.totalIso F W (RelativeCech.ReindexTotal.pushed f K)).hom q ≫
      homologyMap (RelativeCech.ReindexTotal.sourceTotalIso f (F.obj (⊤_ C)) (F.obj ∘ W) K).hom q =
    homologyMap (AugmentedCech.AmbientTotal.totalIso (CechPushforwardCoordinates.pulled f F) W K).hom q := by
  simpa only [homologyMap_comp] using congrArg (fun a => homologyMap a q) (total f F W K)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CechPushforwardTotal.Coordinates
