import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.CoefficientTotal
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.OrderedCechEdge

/-! # Edge Coefficient -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Ordered.EdgeCoefficient

noncomputable section

/-! Coefficient change preserves the literal global-section edge of
the ordered Čech total. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex Opposite _root_.TopologicalSpace
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u vA uA vB uB
variable {X : TopCat.{u}} {ι : Type u} [LinearOrder ι] (U : ι → Opens X)
  {A : Type uA} [Category.{vA} A] [Preadditive A] [HasProducts.{u} A]
  {B : Type uB} [Category.{vB} B] [Preadditive B] [HasProducts.{u} B]
  (G : A ⥤ B) [G.Additive] [PreservesLimitsOfSize.{u,u} G]
  (P : (Opens X)ᵒᵖ ⥤ A)

omit [Preadditive A] [Preadditive B] [G.Additive] in
theorem augmentation :
    G.map (Presheaf.OrderedCechEdge.augmentation U P) ≫
      (AugmentedCech.CoefficientChange.objectIso U G P 1).hom =
    Presheaf.OrderedCechEdge.augmentation U (P ⋙ G) := by
  apply Pi.hom_ext
  intro j
  let f := fun b : AugmentedOrdered.Cech.Index ι 1 =>
    P.obj (op ((AugmentedOrdered.Cech.formal U 1).obj b))
  change (G.map (Presheaf.OrderedCechEdge.augmentation U P) ≫
    piComparison G f) ≫ Pi.π (fun b => G.obj (f b)) j =
      Presheaf.OrderedCechEdge.augmentation U (P ⋙ G) ≫
        Pi.π (fun b => G.obj (f b)) j
  rw [Category.assoc, piComparison_comp_π, ← G.map_comp,
    Presheaf.OrderedCechEdge.augmentation_projection]
  exact (Presheaf.OrderedCechEdge.augmentation_projection U (P ⋙ G) j).symm

variable [HasCoproducts.{0} A] [HasCoproducts.{0} B] [HasFiniteBiproducts A]
  (K : CochainComplex ((Opens X)ᵒᵖ ⥤ A) ℕ)

local notation "L" => OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.OrderedCechEdge.bicomplex U K
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.OrderedCechEdge.sections K
local notation "a" => (fun q => OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.OrderedCechEdge.augmentation U (K.X q))
local notation "ha" => (fun q q' _ =>
  Presheaf.OrderedCechEdge.augmentation_comm U K q q')
local notation "wa" => OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.OrderedCechEdge.augmentation_cocycle U K
local notation "K'" => OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.CoefficientTotal.mapped G K

theorem edge :
    (G.mapHomologicalComplex (.up ℕ)).map (Presheaf.OrderedCechEdge.edge U K) ≫
      (OrderedCech.CoefficientTotal.totalIso U G K).hom =
    Presheaf.OrderedCechEdge.edge U K' := by
  let T := AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison.FiniteTotalComparison.iso G L
  let b := (OrderedCech.CoefficientTotal.bicomplexIso U G K).hom
  have hm := AlgebraicGeometry.Comparison.Betti.TotalComplexEdge.mappedHorizontalEdge_comp_totalComparison G L S a ha wa
  have hn := BicomplexHorizontalEdge.naturality
    (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex G L) ((G.mapHomologicalComplex (.up ℕ)).obj S)
    (fun q => G.map (a q)) (AlgebraicGeometry.Comparison.Betti.TotalComplexEdge.mappedHorizontalAugmentation_comm G L S a ha)
    (AlgebraicGeometry.Comparison.Betti.TotalComplexEdge.mappedHorizontalAugmentation_comp_d G L S a wa)
    (Presheaf.OrderedCechEdge.bicomplex U K') (Presheaf.OrderedCechEdge.sections K')
    (fun q => Presheaf.OrderedCechEdge.augmentation U ((K').X q))
    (fun q q' _ => Presheaf.OrderedCechEdge.augmentation_comm U K' q q')
    (Presheaf.OrderedCechEdge.augmentation_cocycle U K') b (𝟙 _) (fun q => by
      change G.map (a q) ≫ (AugmentedCech.CoefficientChange.objectIso U G (K.X q) 1).hom =
        𝟙 _ ≫ Presheaf.OrderedCechEdge.augmentation U (K.X q ⋙ G)
      rw [Category.id_comp]
      exact augmentation U G (K.X q))
  change (G.mapHomologicalComplex (.up ℕ)).map (Presheaf.OrderedCechEdge.edge U K) ≫
    (T.inv ≫ HomologicalComplex₂.total.map b (.up ℕ)) = _
  calc
    _ = (AlgebraicGeometry.Comparison.Betti.TotalComplexEdge.mappedHorizontalEdge G L S a ha wa ≫ T.hom) ≫
        (T.inv ≫ HomologicalComplex₂.total.map b (.up ℕ)) :=
      congrArg (· ≫ (T.inv ≫ HomologicalComplex₂.total.map b (.up ℕ))) hm.symm
    _ = AlgebraicGeometry.Comparison.Betti.TotalComplexEdge.mappedHorizontalEdge G L S a ha wa ≫
        HomologicalComplex₂.total.map b (.up ℕ) := by simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = _ := by
      dsimp only [AlgebraicGeometry.Comparison.Betti.TotalComplexEdge.mappedHorizontalEdge, Presheaf.OrderedCechEdge.edge,
        Presheaf.OrderedCechEdge.bicomplex, OrderedCech.CoefficientTotal.bicomplex] at hn ⊢
      exact hn.trans (Category.id_comp _)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Ordered.EdgeCoefficient
