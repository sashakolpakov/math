import OAI.AlgebraicGeometry.CycleClass.Thom.Product.NormalPair

/-! # Normal Restriction -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Product.NormalRestriction.Constructions

noncomputable section

/-! The product of the two actual normal classes restricts to the actual
normal class of the constructed product immersion chart. -/

open _root_.CategoryTheory
open OAI.AlgebraicGeometry.CycleClass.Thom.Normal.Product.Constructions.Class
open OAI.AlgebraicGeometry.CycleClass.Thom.Product.NormalPair.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {M N M' N' E F : Type} [TopologicalSpace N] [TopologicalSpace N']
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  {p q : ℕ} {u : M → N} {v : M' → N'} {x : M} {y : M'}
  (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin p → ℂ) u x)
  (Q : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair F (Fin q → ℂ) v y)
  (e : ((Fin p → ℂ) × (Fin q → ℂ)) ≃L[ℂ] (Fin (p + q) → ℂ))

def productNormalInclusion :
    TopCat.of (NormalPair.Constructions.productNormalPair P Q e).neighborhood ⟶
      TopCat.of (P.neighborhood × Q.neighborhood) :=
  TopCat.ofHom ⟨fun z =>
    (⟨z.val.1, (NormalPair.Constructions.productNormalPair_neighborhood_subset P Q e z.property).1⟩,
      ⟨z.val.2, (NormalPair.Constructions.productNormalPair_neighborhood_subset P Q e z.property).2⟩),
    ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
      ((continuous_snd.comp continuous_subtype_val).subtype_mk _)⟩

theorem productNormalInclusion_mapsTo :
    Set.MapsTo (productNormalInclusion P Q e) (NormalPair.Constructions.productNormalPair P Q e).relativeComplement
      (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement (TopCat.of P.neighborhood) (TopCat.of Q.neighborhood)
        P.relativeComplement Q.relativeComplement) := by
  classical
  intro z hz
  change z.val.1 ∉ Set.range u ∨ z.val.2 ∉ Set.range v
  change z.val ∉ Set.range (Prod.map u v) at hz
  simpa only [Set.range_prodMap, Set.mem_prod, not_and_or] using hz

theorem productNormalInclusion_normalCoordinate :
    productNormalInclusion P Q e ≫ Normal.Product.Constructions.Class.combinedNormalMap P.normalCoordinate Q.normalCoordinate e =
      (NormalPair.Constructions.productNormalPair P Q e).normalCoordinate := by
  ext z
  rfl

variable [NormedSpace ℝ E] [NormedSpace ℝ F]

/-- The genuine product normal-pair class is the actual restriction of the
exterior cup of the two genuine factor normal-pair classes. -/
theorem productNormalClass_restriction :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (productNormalInclusion P Q e)
      (productNormalInclusion_mapsTo P Q e) (2 * (p + q))
      (eqToHom (congrArg (fun n => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
        (TopCat.of (P.neighborhood × Q.neighborhood))
        (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement (TopCat.of P.neighborhood) (TopCat.of Q.neighborhood)
          P.relativeComplement Q.relativeComplement) n) (Nat.mul_add 2 p q).symm)
        (HodgeConjecture.DegreeTwo.ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup (TopCat.of P.neighborhood) (TopCat.of Q.neighborhood)
          P.relativeComplement Q.relativeComplement
          (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPair_relativeComplement_isOpen P) (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPair_relativeComplement_isOpen Q)
          (2 * p) (2 * q) P.rationalClassFin Q.rationalClassFin)) =
      (NormalPair.Constructions.productNormalPair P Q e).rationalClassFin := by
  rw [P.rationalClassFin_eq_normalPullback, Q.rationalClassFin_eq_normalPullback,
    (NormalPair.Constructions.productNormalPair P Q e).rationalClassFin_eq_normalPullback]
  simp only [ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.normalCohomologyMap]
  rw [Normal.Product.Constructions.Class.relativeExteriorCup_combinedNormalPullback P.normalCoordinate Q.normalCoordinate
    P.normalCoordinate_mapsTo Q.normalCoordinate_mapsTo
    (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPair_relativeComplement_isOpen P) (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPair_relativeComplement_isOpen Q) e]
  have h := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ)
      (productNormalInclusion P Q e) (Normal.Product.Constructions.Class.combinedNormalMap P.normalCoordinate Q.normalCoordinate e)
      (productNormalInclusion_mapsTo P Q e)
      (Normal.Product.Constructions.Class.combinedNormalMapsTo P.normalCoordinate Q.normalCoordinate
        P.normalCoordinate_mapsTo Q.normalCoordinate_mapsTo e) (2 * (p + q)))
    (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass (p + q))
  simpa only [productNormalInclusion_normalCoordinate P Q e, ConcreteCategory.comp_apply] using h

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Product.NormalRestriction.Constructions
