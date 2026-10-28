import OAI.AlgebraicGeometry.CycleClass.Thom.ExteriorImageCup
import OAI.AlgebraicGeometry.CycleClass.Thom.Product.NormalRestriction
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologySections

/-! # Image Exterior Normal Restriction -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.ImageExteriorNormalRestriction.Constructions

noncomputable section

/-! Global supported exterior cups have the prescribed genuine normal
class on the constructed product normal neighborhood. -/

open _root_.CategoryTheory OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologySections.Cycles
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels
open OAI.AlgebraicGeometry.CycleClass.Thom.ExteriorImageCup.Constructions.Even OAI.AlgebraicGeometry.CycleClass.Thom.ExteriorImageCup.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Product.NormalPair.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Product.NormalRestriction.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {M N M' N' E F : Type} [TopologicalSpace N] [TopologicalSpace N']
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  {p q : ℕ} {u : M → N} {v : M' → N'} {x : M} {y : M'}
  (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin p → ℂ) u x)
  (Q : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair F (Fin q → ℂ) v y)

def normalProductAmbientMap :
    TopCat.of (P.neighborhood × Q.neighborhood) ⟶ TopCat.of (N × N') :=
  AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N) P.neighborhood,
    Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N') Q.neighborhood) :
      (TopCat.of P.neighborhood, TopCat.of Q.neighborhood) ⟶ (TopCat.of N, TopCat.of N'))

omit [NormedSpace ℂ E] [NormedSpace ℂ F] in
theorem normalProductAmbientMapsTo :
    Set.MapsTo (normalProductAmbientMap P Q)
      (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement (TopCat.of P.neighborhood) (TopCat.of Q.neighborhood)
        P.relativeComplement Q.relativeComplement) (Set.range (Prod.map u v))ᶜ :=
  ExteriorImageCup.Constructions.imageProductMapsTo u v (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N) P.neighborhood)
    (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N') Q.neighborhood) (fun _ hz => hz) (fun _ hz => hz)

variable (e : ((Fin p → ℂ) × (Fin q → ℂ)) ≃L[ℂ] (Fin (p + q) → ℂ))

theorem normalProductAmbientMap_comp :
    Product.NormalRestriction.Constructions.productNormalInclusion P Q e ≫ normalProductAmbientMap P Q =
      Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (N × N')) (Product.NormalPair.Constructions.productNormalPair P Q e).neighborhood := by
  ext z <;> rfl

theorem normalProductAmbientMap_restriction (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (normalProductAmbientMap P Q)
      (normalProductAmbientMapsTo P Q) n ≫
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (Product.NormalRestriction.Constructions.productNormalInclusion P Q e)
      (Product.NormalRestriction.Constructions.productNormalInclusion_mapsTo P Q e) n =
    Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of (N × N'))
      (Set.range (Prod.map u v))ᶜ (Product.NormalPair.Constructions.productNormalPair P Q e).openNeighborhood n := by
  have h := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ)
    (Product.NormalRestriction.Constructions.productNormalInclusion P Q e) (normalProductAmbientMap P Q)
    (Product.NormalRestriction.Constructions.productNormalInclusion_mapsTo P Q e) (normalProductAmbientMapsTo P Q) n
  simp only [normalProductAmbientMap_comp P Q e] at h
  exact h

variable [NormedSpace ℝ E] [NormedSpace ℝ F]

theorem imageExteriorCup_normal_restriction
    (hu : IsOpen (Set.range u)ᶜ) (hv : IsOpen (Set.range v)ᶜ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range u)ᶜ (2 * p))
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N') (Set.range v)ᶜ (2 * q))
    (ha : Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of N)
      (Set.range u)ᶜ P.openNeighborhood (2 * p) a = P.rationalClassFin)
    (hb : Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of N')
      (Set.range v)ᶜ Q.openNeighborhood (2 * q) b = Q.rationalClassFin) :
    Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of (N × N'))
      (Set.range (Prod.map u v))ᶜ (Product.NormalPair.Constructions.productNormalPair P Q e).openNeighborhood (2 * (p + q))
      (ExteriorImageCup.Constructions.imageExteriorCup u v hu hv p q a b) = (Product.NormalPair.Constructions.productNormalPair P Q e).rationalClassFin := by
  have hn := ExteriorImageCup.Constructions.imageExteriorCup_naturality u v
    (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N) P.neighborhood)
    (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N') Q.neighborhood)
    (A := P.relativeComplement) (B := Q.relativeComplement)
    (fun _ hz => hz) (fun _ hz => hz)
    (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPair_relativeComplement_isOpen P) (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPair_relativeComplement_isOpen Q)
    hu hv p q a b
  change AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (normalProductAmbientMap P Q)
    (normalProductAmbientMapsTo P Q) (2 * (p + q)) (ExteriorImageCup.Constructions.imageExteriorCup u v hu hv p q a b) =
    ExteriorImageCup.Constructions.Even.evenExteriorCup (TopCat.of P.neighborhood) (TopCat.of Q.neighborhood)
      P.relativeComplement Q.relativeComplement
      (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPair_relativeComplement_isOpen P) (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPair_relativeComplement_isOpen Q) p q
      (Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of N)
        (Set.range u)ᶜ P.openNeighborhood (2 * p) a)
      (Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of N')
        (Set.range v)ᶜ Q.openNeighborhood (2 * q) b) at hn
  rw [ha, hb] at hn
  have hc := ConcreteCategory.congr_hom (normalProductAmbientMap_restriction P Q e (2 * (p + q)))
    (ExteriorImageCup.Constructions.imageExteriorCup u v hu hv p q a b)
  exact hc.symm.trans ((congrArg
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (Product.NormalRestriction.Constructions.productNormalInclusion P Q e)
      (Product.NormalRestriction.Constructions.productNormalInclusion_mapsTo P Q e) (2 * (p + q))) hn).trans
    (Product.NormalRestriction.Constructions.productNormalClass_restriction P Q e))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.ImageExteriorNormalRestriction.Constructions
