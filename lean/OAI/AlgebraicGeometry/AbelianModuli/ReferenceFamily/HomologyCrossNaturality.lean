import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HomologyTensorNaturality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HomologyCrossPairing
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCrossSupport
import OAI.AlgebraicTopology.Kunneth.Add

/-! # Homology Cross Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HomologyCrossNaturality

noncomputable section

section

/-! Naturality of the original normalized singular homology cross
product in degree (1,1), including two independently varying factors. -/

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open OAI.AlgebraicTopology.Kunneth.Add.Construction OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels
open scoped TensorProduct

def productHomologyCross11 (X Y : TopCat.{0}) : HomologyCrossPairing.firstHomology X ⊗[ℚ] HomologyCrossPairing.firstHomology Y →ₗ[ℚ]
    (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (X × Y))).homology 2 :=
  (homologyMap (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.singularChainCross ℚ X Y) 2).hom.comp
    (HomologyTensorNaturality.tensorHomology11 (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X) (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) Y))

theorem productHomologyCross11_self (X : TopCat.{0}) :
    productHomologyCross11 X X = HomologyCrossPairing.homologyCross11 X := rfl

theorem productHomologyCross11_naturality {X X' Y Y' : TopCat.{0}}
    (f : X ⟶ X') (g : Y ⟶ Y') (x : HomologyCrossPairing.firstHomology X) (y : HomologyCrossPairing.firstHomology Y) :
    homologyMap ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains ℚ).map (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f, g) : (X, Y) ⟶ (X', Y')))) 2
      (productHomologyCross11 X Y (x ⊗ₜ[ℚ] y)) =
    productHomologyCross11 X' Y'
      (homologyMap ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains ℚ).map f) 1 x ⊗ₜ[ℚ] homologyMap ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains ℚ).map g) 1 y) := by
  have hn : (((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains ℚ).map f ⊗ₘ (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains ℚ).map g) ≫ HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.singularChainCross ℚ X' Y') =
      HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.singularChainCross ℚ X Y ≫ (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains ℚ).map (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f, g) : (X, Y) ⟶ (X', Y'))) :=
    HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.singularChainCross_naturality ℚ f g
  have h := (homologyMap_comp ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains ℚ).map f ⊗ₘ (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains ℚ).map g)
    (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.singularChainCross ℚ X' Y') 2).symm.trans
      ((congrArg (fun a => homologyMap a 2) hn).trans
        (homologyMap_comp (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.singularChainCross ℚ X Y)
          ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains ℚ).map (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f, g) : (X, Y) ⟶ (X', Y')))) 2))
  have hv := ConcreteCategory.congr_hom h
    (HomologyTensorNaturality.tensorHomology11 (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X) (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) Y) (x ⊗ₜ[ℚ] y))
  change _ = homologyMap ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains ℚ).map (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f, g) : (X, Y) ⟶ (X', Y')))) 2
    (productHomologyCross11 X Y (x ⊗ₜ[ℚ] y)) at hv
  refine hv.symm.trans ?_
  exact congrArg (homologyMap (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.singularChainCross ℚ X' Y') 2)
    (HomologyTensorNaturality.tensorHomology11_naturality ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains ℚ).map f) ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains ℚ).map g) x y)

end

/-! Either projection kills the degree-(1,1) homology cross product.
Factor the projection through a product with a point and use the
actual vanishing of positive singular homology of that point. -/

open _root_.CategoryTheory _root_.HomologicalComplex
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels
open scoped TensorProduct

theorem singularHomology_comp {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (n : ℕ) (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology n) :
    homologyMap ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains ℚ).map (f ≫ g)) n z =
      homologyMap ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains ℚ).map g) n (homologyMap ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains ℚ).map f) n z) :=
  ConcreteCategory.congr_hom
    ((congrArg (fun a => homologyMap a n) ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains ℚ).map_comp f g)).trans
      (homologyMap_comp ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains ℚ).map f) ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains ℚ).map g) n)) z

theorem point_firstHomology_zero (x : HomologyCrossPairing.firstHomology (TopCat.of Unit)) : x = 0 := by
  let : Subsingleton (HomologyCrossPairing.firstHomology (TopCat.of Unit)) := ModuleCat.subsingleton_of_isZero
    (CycleClass.Geometric.ContractibleModel.Cycles.isZero_singularHomology_of_contractible (ModuleCat.of ℚ ℚ) (TopCat.of Unit) 1 (by decide))
  exact Subsingleton.elim _ _

theorem productHomologyCross11_fst (X Y : TopCat.{0}) (x : HomologyCrossPairing.firstHomology X) (y : HomologyCrossPairing.firstHomology Y) :
    homologyMap ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains ℚ).map (TopCat.prodFst : TopCat.of (X × Y) ⟶ X)) 2
      (productHomologyCross11 X Y (x ⊗ₜ[ℚ] y)) = 0 := by
  let u : Y ⟶ TopCat.of Unit := TopCat.ofHom ⟨fun _ => (), continuous_const⟩
  let f := AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((𝟙 X, u) : (X, Y) ⟶ (X, TopCat.of Unit))
  have h := productHomologyCross11_naturality (𝟙 X) u x y
  rw [point_firstHomology_zero (homologyMap ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains ℚ).map u) 1 y)] at h
  have hz : productHomologyCross11 X (TopCat.of Unit)
      (homologyMap ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains ℚ).map (𝟙 X)) 1 x ⊗ₜ[ℚ] (0 : HomologyCrossPairing.firstHomology (TopCat.of Unit))) = 0 :=
    (congrArg (productHomologyCross11 X (TopCat.of Unit))
      (TensorProduct.tmul_zero (HomologyCrossPairing.firstHomology (TopCat.of Unit)) _)).trans (map_zero _)
  have h0 := h.trans hz
  have hc := singularHomology_comp f (TopCat.prodFst (X := X) (Y := TopCat.of Unit)) 2
    (productHomologyCross11 X Y (x ⊗ₜ[ℚ] y))
  have he : f ≫ (TopCat.prodFst (X := X) (Y := TopCat.of Unit)) = TopCat.prodFst := rfl
  rw [he] at hc
  exact hc.trans ((congrArg (homologyMap ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains ℚ).map
    (TopCat.prodFst (X := X) (Y := TopCat.of Unit))) 2) h0).trans (map_zero _))

theorem productHomologyCross11_snd (X Y : TopCat.{0}) (x : HomologyCrossPairing.firstHomology X) (y : HomologyCrossPairing.firstHomology Y) :
    homologyMap ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains ℚ).map (TopCat.prodSnd : TopCat.of (X × Y) ⟶ Y)) 2
      (productHomologyCross11 X Y (x ⊗ₜ[ℚ] y)) = 0 := by
  let u : X ⟶ TopCat.of Unit := TopCat.ofHom ⟨fun _ => (), continuous_const⟩
  let f := AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((u, 𝟙 Y) : (X, Y) ⟶ (TopCat.of Unit, Y))
  have h := productHomologyCross11_naturality u (𝟙 Y) x y
  rw [point_firstHomology_zero (homologyMap ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains ℚ).map u) 1 x)] at h
  have hz : productHomologyCross11 (TopCat.of Unit) Y
      ((0 : HomologyCrossPairing.firstHomology (TopCat.of Unit)) ⊗ₜ[ℚ] homologyMap ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains ℚ).map (𝟙 Y)) 1 y) = 0 :=
    (congrArg (productHomologyCross11 (TopCat.of Unit) Y)
      (TensorProduct.zero_tmul (HomologyCrossPairing.firstHomology (TopCat.of Unit)) _)).trans (map_zero _)
  have h0 := h.trans hz
  have hc := singularHomology_comp f (TopCat.prodSnd (X := TopCat.of Unit) (Y := Y)) 2
    (productHomologyCross11 X Y (x ⊗ₜ[ℚ] y))
  have he : f ≫ (TopCat.prodSnd (X := TopCat.of Unit) (Y := Y)) = TopCat.prodSnd := rfl
  rw [he] at hc
  exact hc.trans ((congrArg (homologyMap ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains ℚ).map
    (TopCat.prodSnd (X := TopCat.of Unit) (Y := Y))) 2) h0).trans (map_zero _))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HomologyCrossNaturality
