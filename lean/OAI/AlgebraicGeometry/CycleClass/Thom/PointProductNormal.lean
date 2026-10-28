import OAI.AlgebraicGeometry.CycleClass.Thom.Supported.PointProjection
import OAI.AlgebraicGeometry.CycleClass.Thom.CanonicalLocalDualCoordinates
import OAI.AlgebraicGeometry.CycleClass.Thom.Normal.Product

/-! # Point Product Normal -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.PointProductNormal.Constructions.Class

noncomputable section

/-! The product point class is the original normal class in concatenated translated coordinates. -/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.CycleClass.Thom.Supported.PointProjection.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.CanonicalLocalDualCoordinates.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normal.Product.Constructions.Class

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def translation (d : ℕ) (x : Fin d → ℂ) : TopCat.of (Fin d → ℂ) ⟶ TopCat.of (Fin d → ℂ) :=
  (TopCat.isoOfHomeo (X := TopCat.of (Fin d → ℂ))
    (Y := TopCat.of (Fin d → ℂ)) (Homeomorph.subRight x)).hom

def normalPointMap (p d : ℕ) (x : Fin d → ℂ)
    (e : ((Fin p → ℂ) × (Fin d → ℂ)) ≃L[ℂ] (Fin (p + d) → ℂ)) :
    TopCat.of ((Fin p → ℂ) × (Fin d → ℂ)) ⟶ TopCat.of (Fin (p + d) → ℂ) :=
  Normal.Product.Constructions.Class.combinedNormalMap (𝟙 (TopCat.of (Fin p → ℂ))) (translation d x) e

theorem normalPointMapsTo (p d : ℕ) (x : Fin d → ℂ)
    (e : ((Fin p → ℂ) × (Fin d → ℂ)) ≃L[ℂ] (Fin (p + d) → ℂ)) :
    Set.MapsTo (normalPointMap p d x e) (({0} : Set (Fin p → ℂ)) ×ˢ {x})ᶜ ({0}ᶜ) :=
  (Normal.Product.Constructions.Class.combinedNormalMapsTo (X := TopCat.of (Fin p → ℂ)) (Y := TopCat.of (Fin d → ℂ))
    (𝟙 (TopCat.of (Fin p → ℂ))) (translation d x)
    (A := {0}ᶜ) (B := {x}ᶜ) (fun _ hz => hz) (CanonicalLocalDualCoordinates.Constructions.translationMapsTo d x) e).comp
    (Supported.PointProjection.Constructions.productComplementMapsTo (TopCat.of (Fin p → ℂ)) (TopCat.of (Fin d → ℂ)) {0} {x})

theorem productPointClass_normal (p d : ℕ) (x : Fin d → ℂ)
    (e : ((Fin p → ℂ) × (Fin d → ℂ)) ≃L[ℂ] (Fin (p + d) → ℂ)) :
    eqToHom (congrArg (fun n => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of ((Fin p → ℂ) × (Fin d → ℂ))) (({0} : Set (Fin p → ℂ)) ×ˢ {x})ᶜ n)
      (Nat.mul_add 2 p d).symm)
      (Supported.PointProjection.Constructions.productPointClass d (TopCat.of (Fin p → ℂ)) {0} isClosed_singleton x (2 * p)
        (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass p)) =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (normalPointMap p d x e)
        (normalPointMapsTo p d x e) (2 * (p + d)) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass (p + d)) := by
  have h := Normal.Product.Constructions.Class.relativeExteriorCup_combinedNormalPullback
    (X := TopCat.of (Fin p → ℂ)) (Y := TopCat.of (Fin d → ℂ)) (𝟙 (TopCat.of (Fin p → ℂ)))
    (translation d x) (A := {0}ᶜ) (B := {x}ᶜ) (fun _ hz => hz) (CanonicalLocalDualCoordinates.Constructions.translationMapsTo d x)
    isClosed_singleton.isOpen_compl isClosed_singleton.isOpen_compl e
  simp only [AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_id, CategoryTheory.id_apply] at h
  rw [show AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (translation d x)
    (CanonicalLocalDualCoordinates.Constructions.translationMapsTo d x) (2 * d) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass d) =
      CanonicalLocalDual.Constructions.canonicalLocalDual d x from CanonicalLocalDualCoordinates.Constructions.canonicalLocalDual_translation d x] at h
  rw [Supported.PointProjection.Constructions.productPointClass, Normal.Product.Constructions.Class.relativeCohomologyMap_degreeCast
    (𝟙 (TopCat.of ((Fin p → ℂ) × (Fin d → ℂ))))
    (Supported.PointProjection.Constructions.productComplementMapsTo (TopCat.of (Fin p → ℂ)) (TopCat.of (Fin d → ℂ)) {0} {x})
    (Nat.mul_add 2 p d).symm]
  refine (congrArg (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
    (𝟙 (TopCat.of ((Fin p → ℂ) × (Fin d → ℂ))))
    (Supported.PointProjection.Constructions.productComplementMapsTo (TopCat.of (Fin p → ℂ)) (TopCat.of (Fin d → ℂ)) {0} {x})
    (2 * (p + d))) h).trans ?_
  exact ConcreteCategory.congr_hom (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ)
    (𝟙 (TopCat.of ((Fin p → ℂ) × (Fin d → ℂ)))) (normalPointMap p d x e)
    (Supported.PointProjection.Constructions.productComplementMapsTo (TopCat.of (Fin p → ℂ)) (TopCat.of (Fin d → ℂ)) {0} {x})
    (Normal.Product.Constructions.Class.combinedNormalMapsTo (X := TopCat.of (Fin p → ℂ)) (Y := TopCat.of (Fin d → ℂ))
      (𝟙 (TopCat.of (Fin p → ℂ))) (translation d x)
      (A := {0}ᶜ) (B := {x}ᶜ) (fun _ hz => hz) (CanonicalLocalDualCoordinates.Constructions.translationMapsTo d x) e)
    (2 * (p + d))) _

end

end OAI.AlgebraicGeometry.CycleClass.Thom.PointProductNormal.Constructions.Class
