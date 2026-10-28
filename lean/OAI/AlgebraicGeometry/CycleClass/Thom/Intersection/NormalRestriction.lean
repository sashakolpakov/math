import OAI.AlgebraicGeometry.CycleClass.Thom.ImageExteriorNormalRestriction
import OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionCup

/-! # Normal Restriction -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.NormalRestriction.Constructions

noncomputable section

/-! The actual supported cup restricts to the normalized class in
simultaneous normal coordinates. The hypotheses describe actual charts
and their normal-coordinate functions. -/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels

open OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionCup.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ExteriorImageCup.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ExteriorImageCup.Constructions.Even
  Normal.Product.Constructions.Class ImageExteriorNormalRestriction.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {M L T N E F D : Type} [TopologicalSpace N]
  [NormedAddCommGroup E]
  [NormedAddCommGroup F]
  [NormedAddCommGroup D]
  {p q : ℕ} {u : M → N} {v : L → N} {w : T → N} {x : M} {y : L} {z : T}
  (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin p → ℂ) u x)
  (Q : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair F (Fin q → ℂ) v y)
  (R : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair D (Fin (p + q) → ℂ) w z)
  (hw : Set.range w = Set.range u ∩ Set.range v)
  (hR : R.neighborhood ⊆ P.neighborhood ∩ Q.neighborhood)
  (e : ((Fin p → ℂ) × (Fin q → ℂ)) ≃L[ℂ] (Fin (p + q) → ℂ))

def intersectionNormalInclusion : TopCat.of R.neighborhood ⟶
    TopCat.of (P.neighborhood × Q.neighborhood) :=
  TopCat.ofHom ⟨fun a => (⟨a.val, (hR a.property).1⟩, ⟨a.val, (hR a.property).2⟩),
    (continuous_subtype_val.subtype_mk _).prodMk (continuous_subtype_val.subtype_mk _)⟩

include hw in
theorem intersectionNormalInclusion_mapsTo :
    Set.MapsTo (intersectionNormalInclusion P Q R hR) R.relativeComplement
      (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement (TopCat.of P.neighborhood) (TopCat.of Q.neighborhood)
        P.relativeComplement Q.relativeComplement) := by
  intro a ha
  change a.val ∉ Set.range u ∨ a.val ∉ Set.range v
  change a.val ∉ Set.range w at ha
  simpa only [hw, Set.mem_inter_iff, not_and_or] using ha

include hw in
theorem intersectionNeighborhood_mapsTo :
    Set.MapsTo (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N) R.neighborhood) R.relativeComplement
      (Set.range u ∩ Set.range v)ᶜ := by
  intro a ha
  change a.val ∉ Set.range u ∩ Set.range v
  rwa [← hw]

variable (hn : ∀ a : R.neighborhood, R.normalCoordinate a =
  e ((P.ambientChart a.val).2, (Q.ambientChart a.val).2))

include hn hR

theorem intersectionNormalInclusion_normalCoordinate :
    intersectionNormalInclusion P Q R hR ≫ Normal.Product.Constructions.Class.combinedNormalMap P.normalCoordinate Q.normalCoordinate e =
      R.normalCoordinate := by
  ext a i
  exact congrFun (hn a).symm i

variable [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ D]

theorem intersectionNormalClass_restriction :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (intersectionNormalInclusion P Q R hR)
      (intersectionNormalInclusion_mapsTo P Q R hw hR) (2 * (p + q))
      (ExteriorImageCup.Constructions.Even.evenExteriorCup (TopCat.of P.neighborhood) (TopCat.of Q.neighborhood)
        P.relativeComplement Q.relativeComplement
        (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPair_relativeComplement_isOpen P) (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPair_relativeComplement_isOpen Q)
        p q P.rationalClassFin Q.rationalClassFin) = R.rationalClassFin := by
  rw [P.rationalClassFin_eq_normalPullback, Q.rationalClassFin_eq_normalPullback,
    R.rationalClassFin_eq_normalPullback]
  simp only [ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.normalCohomologyMap]
  rw [show ExteriorImageCup.Constructions.Even.evenExteriorCup (TopCat.of P.neighborhood) (TopCat.of Q.neighborhood)
      P.relativeComplement Q.relativeComplement
      (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPair_relativeComplement_isOpen P) (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPair_relativeComplement_isOpen Q) p q _ _ =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
        (Normal.Product.Constructions.Class.combinedNormalMap P.normalCoordinate Q.normalCoordinate e)
        (Normal.Product.Constructions.Class.combinedNormalMapsTo P.normalCoordinate Q.normalCoordinate
          P.normalCoordinate_mapsTo Q.normalCoordinate_mapsTo e) (2 * (p + q))
        (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass (p + q)) from
    Normal.Product.Constructions.Class.relativeExteriorCup_combinedNormalPullback P.normalCoordinate Q.normalCoordinate
      P.normalCoordinate_mapsTo Q.normalCoordinate_mapsTo
      (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPair_relativeComplement_isOpen P) (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPair_relativeComplement_isOpen Q) e]
  have h := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ)
      (intersectionNormalInclusion P Q R hR) (Normal.Product.Constructions.Class.combinedNormalMap P.normalCoordinate Q.normalCoordinate e)
      (intersectionNormalInclusion_mapsTo P Q R hw hR)
      (Normal.Product.Constructions.Class.combinedNormalMapsTo P.normalCoordinate Q.normalCoordinate
        P.normalCoordinate_mapsTo Q.normalCoordinate_mapsTo e) (2 * (p + q)))
    (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass (p + q))
  simpa only [intersectionNormalInclusion_normalCoordinate P Q R hR e hn,
    ConcreteCategory.comp_apply] using h

theorem imageIntersectionCup_normal_restriction
    (hu : IsOpen (Set.range u)ᶜ) (hv : IsOpen (Set.range v)ᶜ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range u)ᶜ (2 * p))
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range v)ᶜ (2 * q))
    (ha : Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of N)
      (Set.range u)ᶜ P.openNeighborhood (2 * p) a = P.rationalClassFin)
    (hb : Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of N)
      (Set.range v)ᶜ Q.openNeighborhood (2 * q) b = Q.rationalClassFin) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N) R.neighborhood)
      (intersectionNeighborhood_mapsTo R hw) (2 * (p + q))
      (ImageIntersectionCup.Constructions.imageIntersectionCup u v hu hv p q a b) = R.rationalClassFin := by
  have h₁ := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ)
    (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N) R.neighborhood) (ImageIntersectionCup.Constructions.diagonalMap (TopCat.of N))
    (intersectionNeighborhood_mapsTo R hw) (ImageIntersectionCup.Constructions.diagonalMap_complement u v) (2 * (p + q))
  have h₂ := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ)
    (intersectionNormalInclusion P Q R hR) (ImageExteriorNormalRestriction.Constructions.normalProductAmbientMap P Q)
    (intersectionNormalInclusion_mapsTo P Q R hw hR)
    (ImageExteriorNormalRestriction.Constructions.normalProductAmbientMapsTo P Q) (2 * (p + q))
  have he := ConcreteCategory.congr_hom (h₁.trans h₂.symm) (ExteriorImageCup.Constructions.imageExteriorCup u v hu hv p q a b)
  have ht := ExteriorImageCup.Constructions.imageExteriorCup_naturality u v
    (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N) P.neighborhood)
    (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N) Q.neighborhood)
    (A := P.relativeComplement) (B := Q.relativeComplement)
    (fun _ hz => hz) (fun _ hz => hz)
    (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPair_relativeComplement_isOpen P) (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPair_relativeComplement_isOpen Q)
    hu hv p q a b
  change AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (ImageExteriorNormalRestriction.Constructions.normalProductAmbientMap P Q)
    (ImageExteriorNormalRestriction.Constructions.normalProductAmbientMapsTo P Q) (2 * (p + q)) (ExteriorImageCup.Constructions.imageExteriorCup u v hu hv p q a b) =
    ExteriorImageCup.Constructions.Even.evenExteriorCup (TopCat.of P.neighborhood) (TopCat.of Q.neighborhood)
      P.relativeComplement Q.relativeComplement
      (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPair_relativeComplement_isOpen P) (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPair_relativeComplement_isOpen Q) p q
      (Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of N)
        (Set.range u)ᶜ P.openNeighborhood (2 * p) a)
      (Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of N)
        (Set.range v)ᶜ Q.openNeighborhood (2 * q) b) at ht
  rw [ha, hb] at ht
  exact he.trans ((congrArg
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (intersectionNormalInclusion P Q R hR)
      (intersectionNormalInclusion_mapsTo P Q R hw hR) (2 * (p + q))) ht).trans
    (intersectionNormalClass_restriction P Q R hw hR e hn))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.NormalRestriction.Constructions
