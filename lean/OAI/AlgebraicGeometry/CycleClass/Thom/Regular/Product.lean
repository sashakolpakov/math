import OAI.AlgebraicGeometry.CycleClass.Thom.ExteriorProduct
import OAI.AlgebraicGeometry.CycleClass.Thom.GeometricTrace

/-! # Product -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Regular.Product.Constructions

noncomputable section

/-! The genuine product immersion of two algebraic cycle regular loci.
Its global Thom class has the exterior cup of their geometric classes as
its ordinary image. All manifold and dimension hypotheses are discharged. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Product.Immersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass
open OAI.AlgebraicGeometry.CycleClass.Thom.ExteriorProduct.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ExteriorImageCup.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.ExteriorCupForget.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.GeometricTrace.Constructions.HigherThom
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V W : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p q : ℕ}
  (D : Geometric.DimensionCycles.DimensionCycleSupport V p) (Z : Geometric.DimensionCycles.DimensionCycleSupport W q)

theorem regular_model_finrank_le : Module.finrank ℂ D.regularAnalyticModel ≤
    Module.finrank ℂ V.analyticModel := by
  rw [D.regularAnalyticModel_complex_finrank, V.analyticModel_complex_finrank]
  exact Nat.sub_le _ _

theorem regularThomClass_eq_inDegree : D.regularThomClass =
    Degree.Constructions.ThomClass.complexThomClassInDegree D.regularComplementInclusion (D.contMDiff_regularComplementInclusion ω)
      D.mfderiv_regularComplementInclusion_injective D.isClosedEmbedding_regularComplementInclusion
      p D.regularComplement_complexImmersionCodimension := rfl

/-- The actual global Thom class of the product of the two native closed
regular-locus immersions, in degree twice the sum of algebraic codimensions. -/
def regularProductThomClass :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of (D.regularAmbientSpace × Z.regularAmbientSpace))
      (Set.range (Prod.map D.regularComplementInclusion Z.regularComplementInclusion))ᶜ
      (2 * (p + q)) := by
  letI := Product.Immersion.Constructions.productModelCharted D.regularAnalyticModel D.regularAnalyticSpace
    Z.regularAnalyticModel Z.regularAnalyticSpace
  letI := Product.Immersion.Constructions.productModelCharted V.analyticModel D.regularAmbientSpace
    W.analyticModel Z.regularAmbientSpace
  letI : IsManifold 𝓘(ℂ, D.regularAnalyticModel × Z.regularAnalyticModel) ω
      (D.regularAnalyticSpace × Z.regularAnalyticSpace) := Product.Immersion.Constructions.productModel_isManifold
  letI : IsManifold 𝓘(ℂ, V.analyticModel × W.analyticModel) ω
      (D.regularAmbientSpace × Z.regularAmbientSpace) := Product.Immersion.Constructions.productModel_isManifold
  exact Degree.Constructions.ThomClass.complexThomClassInDegree (Prod.map D.regularComplementInclusion Z.regularComplementInclusion)
    (Product.Immersion.Constructions.productImmersion_contMDiff D.regularComplementInclusion Z.regularComplementInclusion
      (D.contMDiff_regularComplementInclusion ω) (Z.contMDiff_regularComplementInclusion ω))
    (Product.Immersion.Constructions.productImmersion_injective_mfderiv D.regularComplementInclusion Z.regularComplementInclusion
      (D.contMDiff_regularComplementInclusion ω) (Z.contMDiff_regularComplementInclusion ω)
      D.mfderiv_regularComplementInclusion_injective Z.mfderiv_regularComplementInclusion_injective)
    (D.isClosedEmbedding_regularComplementInclusion.prodMap Z.isClosedEmbedding_regularComplementInclusion)
    (p + q) ((Product.Immersion.Constructions.complexImmersionCodimension_prod (regular_model_finrank_le D) (regular_model_finrank_le Z)).trans
      (congrArg₂ (· + ·) D.regularComplement_complexImmersionCodimension
        Z.regularComplement_complexImmersionCodimension))

theorem regularProductThomClass_eq_exterior :
    regularProductThomClass D Z =
    ExteriorImageCup.Constructions.imageExteriorCup D.regularComplementInclusion Z.regularComplementInclusion
      D.isClosedEmbedding_regularComplementInclusion.isClosed_range.isOpen_compl
      Z.isClosedEmbedding_regularComplementInclusion.isClosed_range.isOpen_compl p q
      D.regularThomClass Z.regularThomClass := by
  rw [regularThomClass_eq_inDegree D, regularThomClass_eq_inDegree Z]
  exact (ExteriorProduct.Constructions.complexThomClassInDegree_exteriorProduct D.regularComplementInclusion Z.regularComplementInclusion
    (D.contMDiff_regularComplementInclusion ω) (Z.contMDiff_regularComplementInclusion ω)
    D.mfderiv_regularComplementInclusion_injective Z.mfderiv_regularComplementInclusion_injective
    D.isClosedEmbedding_regularComplementInclusion Z.isClosedEmbedding_regularComplementInclusion
    (regular_model_finrank_le D) (regular_model_finrank_le Z) p q
    D.regularComplement_complexImmersionCodimension Z.regularComplement_complexImmersionCodimension).symm

theorem regularThomClass_forget_geometric :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace)
      (Set.range D.regularComplementInclusion)ᶜ (2 * p) D.regularThomClass =
    eqToHom (congrArg (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace))
      (two_mul p).symm) D.regularGeometricCycleClass := by
  let i := eqToIso (congrArg (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ)
    (TopCat.of D.regularAmbientSpace)) (two_mul p))
  have h : i.hom (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace)
      (Set.range D.regularComplementInclusion)ᶜ (2 * p) D.regularThomClass) =
      D.regularGeometricCycleClass :=
    (GeometricTrace.Constructions.HigherThom.regularAbsoluteThomClass_eq_cast D).symm.trans (GeometricTrace.Constructions.HigherThom.regularAbsoluteThomClass_eq_geometric D)
  exact i.toLinearEquiv.injective (h.trans (i.toLinearEquiv.apply_symm_apply D.regularGeometricCycleClass).symm)

theorem regularProductThomClass_forget_geometric :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ)
      (TopCat.of (D.regularAmbientSpace × Z.regularAmbientSpace))
      (Set.range (Prod.map D.regularComplementInclusion Z.regularComplementInclusion))ᶜ
      (2 * (p + q)) (regularProductThomClass D Z) =
    ExteriorCupForget.Constructions.evenAbsoluteExteriorCup (TopCat.of D.regularAmbientSpace) (TopCat.of Z.regularAmbientSpace) p q
      (eqToHom (congrArg (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace))
        (two_mul p).symm) D.regularGeometricCycleClass)
      (eqToHom (congrArg (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace))
        (two_mul q).symm) Z.regularGeometricCycleClass) := by
  rw [regularProductThomClass_eq_exterior, ExteriorCupForget.Constructions.imageExteriorCup_forget,
    regularThomClass_forget_geometric D, regularThomClass_forget_geometric Z]

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Regular.Product.Constructions
