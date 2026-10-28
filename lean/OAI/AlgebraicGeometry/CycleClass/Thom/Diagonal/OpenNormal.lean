import OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.OpenZero
import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.DiagonalSubmersion
import OAI.AlgebraicGeometry.CycleClass.Thom.BaseOpenLiftAnalytic
import OAI.AlgebraicGeometry.CycleClass.Thom.EquationThomClass
import OAI.AlgebraicGeometry.CycleClass.Thom.BaseVectorNormal

/-! # Open Normal -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.OpenNormal.Constructions

noncomputable section

/-! The exact diagonal section vector used in the Serre local formula
represents the actual diagonal Thom class on a coordinate neighborhood. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped MonoidalCategory TensorProduct _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Ambient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.OpenVector.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.OpenEquations.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.ComplexImmersion.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.OpenZero.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.DiagonalSubmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.DiagonalEvaluation.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.BaseOpenLiftAnalytic.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.BaseSectionVector.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.EtaleSectionVector.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Section.VectorHeadChange.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.BaseVectorNormal.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.BaseVectorNormal.Constructions.SectionSupport OAI.AlgebraicGeometry.CycleClass.Thom.EquationThomClass.Constructions.Raw

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (j : X ⟶ V.toOver)
  [IsAffine X.left] [IsIntegral X.left] [Smooth X.hom] [IsOpenImmersion j.left]

local instance : IsIntegral (X ⊗ X).left := Affine.ProductIs.Constructions.affineProduct_isIntegral X X
local instance : Smooth (X ⊗ X).hom := inferInstanceAs (Smooth (pullback.fst X.hom X.hom ≫ X.hom))
local instance : IsIntegral (Ambient.Constructions.productVariety V V).toOver.left := (Ambient.Constructions.productVariety V V).property
local instance : Smooth (Ambient.Constructions.productVariety V V).toOver.hom := (Ambient.Constructions.productVariety V V).presentation.smooth
local instance : Nonempty (OpenEquations.Constructions.productOpen V X j) :=
  ⟨⟨OpenEquations.Constructions.center V X j (genericPoint X.left), OpenEquations.Constructions.center_mem V X j (genericPoint X.left)⟩⟩

variable (U : Opens (Ambient.Constructions.productVariety V V).analyticSpace)
  (hU : (U : Set (Ambient.Constructions.productVariety V V).analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (OpenVector.Constructions.productOpenOverMap V X j)))
  (hUB : (U : Set (Ambient.Constructions.productVariety V V).analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion (OpenEquations.Constructions.productOpen V X j))))

local instance : ChartedSpace (Ambient.Constructions.productVariety V V).analyticModel U :=
  inferInstanceAs (ChartedSpace (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension
    (Ambient.Constructions.productVariety V V).toOver.hom) → ℂ) U)

section Differential

variable (n : ℕ) [Algebra (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)]
  [IsScalarTower ℂ (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)]

include hU in
theorem diagonalBaseVector_analytic :
    ContMDiff 𝓘(ℂ, (Ambient.Constructions.productVariety V V).analyticModel) 𝓘(ℂ, Fin n → ℂ) ω
      (BaseSectionVector.Constructions.baseSectionVector (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion (OpenEquations.Constructions.productOpen V X j)) U hUB n (OpenEquations.Constructions.diagonalSection V X j n)) := by
  rw [OpenVector.Constructions.diagonalBaseVector_eq V X j n U hU hUB]
  exact (Affine.DiagonalSubmersion.Constructions.diagonalVector_analytic X n).comp (BaseOpenLiftAnalytic.Constructions.baseOpenLift_analytic (OpenVector.Constructions.productOpenOverMap V X j) U hU)

variable [Algebra.FormallyEtale (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)]

include hU in
theorem diagonalBaseVector_submersion (u : U) :
    Function.Surjective (mfderiv 𝓘(ℂ, (Ambient.Constructions.productVariety V V).analyticModel) 𝓘(ℂ, Fin n → ℂ)
      (BaseSectionVector.Constructions.baseSectionVector (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion (OpenEquations.Constructions.productOpen V X j)) U hUB n (OpenEquations.Constructions.diagonalSection V X j n)) u) := by
  rw [OpenVector.Constructions.diagonalBaseVector_eq V X j n U hU hUB]
  have h := mfderiv_comp u ((Affine.DiagonalSubmersion.Constructions.diagonalVector_analytic X n).mdifferentiableAt (by simp))
    ((BaseOpenLiftAnalytic.Constructions.baseOpenLift_analytic (OpenVector.Constructions.productOpenOverMap V X j) U hU).mdifferentiableAt (by simp))
  exact (congrArg (fun L : (Ambient.Constructions.productVariety V V).analyticModel →L[ℂ] (Fin n → ℂ) => Function.Surjective L) h).mpr
    ((Affine.DiagonalSubmersion.Constructions.diagonalVector_submersion X n _).comp
      (BaseOpenLiftAnalytic.Constructions.baseOpenLift_differential_bijective (OpenVector.Constructions.productOpenOverMap V X j) U hU u).2)

end Differential

variable [Algebra (MvPolynomial (Fin V.complexDimension) ℂ) Γ(X.left, ⊤)]
  [IsScalarTower ℂ (MvPolynomial (Fin V.complexDimension) ℂ) Γ(X.left, ⊤)]
  [Algebra.FormallyEtale (MvPolynomial (Fin V.complexDimension) ℂ) Γ(X.left, ⊤)]
  (O : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
  (hi : Set.InjOn (Section.VectorHeadChange.Constructions.sectionVectorEquation X V.complexDimension (EtaleSectionVector.Constructions.coordinateSections X V.complexDimension)) O)
  (hO : ∀ u : U, (Scheme.PointProduct.Constructions.schemePointProductHomeomorph X X
      (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift (OpenVector.Constructions.productOpenOverMap V X j) U hU u)).1 ∈ O ∧
    (Scheme.PointProduct.Constructions.schemePointProductHomeomorph X X
      (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift (OpenVector.Constructions.productOpenOverMap V X j) U hU u)).2 ∈ O)

include hi hO in
omit [Algebra.FormallyEtale (MvPolynomial (Fin V.complexDimension) ℂ) Γ(X.left, ⊤)] in
theorem diagonalEquation_mapsTo :
    Set.MapsTo (BaseSectionVector.Constructions.baseSectionVector (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion (OpenEquations.Constructions.productOpen V X j)) U hUB V.complexDimension
      (OpenEquations.Constructions.diagonalSection V X j V.complexDimension))
      (Set.range (ComplexImmersion.Constructions.diagonalOpenImmersion V U).regularComplementInclusion)ᶜ ({0}ᶜ) :=
  fun u hu hz => hu ((OpenZero.Constructions.diagonalBaseVector_zero_iff V X j U hU hUB V.complexDimension O hi hO u).mpr hz)

theorem diagonalEquation_Thom :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (BaseSectionVector.Constructions.baseSectionVector (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion (OpenEquations.Constructions.productOpen V X j)) U hUB V.complexDimension
        (OpenEquations.Constructions.diagonalSection V X j V.complexDimension))
      (diagonalEquation_mapsTo V X j U hU hUB O hi hO) (2 * V.complexDimension)
      (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass V.complexDimension) = (ComplexImmersion.Constructions.diagonalOpenImmersion V U).regularThomClass := by
  let D := ComplexImmersion.Constructions.diagonalOpenImmersion V U
  exact EquationThomClass.Constructions.Raw.equation_pullback_eq_Thom D.regularComplementInclusion D.holomorphic D.differential_injective D.closed
    V.complexDimension D.regularComplement_complexImmersionCodimension
    (by simpa only [Module.finrank_fin_fun] using D.regularComplexDimension_add_codimension)
    (BaseSectionVector.Constructions.baseSectionVector (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion (OpenEquations.Constructions.productOpen V X j)) U hUB V.complexDimension
      (OpenEquations.Constructions.diagonalSection V X j V.complexDimension))
    (OpenZero.Constructions.diagonalBaseVector_zero_iff V X j U hU hUB V.complexDimension O hi hO)
    (diagonalBaseVector_analytic V X j U hU hUB V.complexDimension)
    (fun _ => diagonalBaseVector_submersion V X j U hU hUB V.complexDimension _)

include hi hO in
omit [Algebra.FormallyEtale (MvPolynomial (Fin V.complexDimension) ℂ) Γ(X.left, ⊤)] in
theorem diagonalNormal_mapsTo : Set.MapsTo (𝟙 (TopCat.of U))
    (Set.range (ComplexImmersion.Constructions.diagonalOpenImmersion V U).regularComplementInclusion)ᶜ
    (Set.range (BaseVectorNormal.Constructions.SectionSupport.vectorZeroImage (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion (OpenEquations.Constructions.productOpen V X j)) U hUB V.complexDimension
      (OpenEquations.Constructions.diagonalSection V X j V.complexDimension)))ᶜ := by
  intro u hu hz
  rw [BaseVectorNormal.Constructions.SectionSupport.vectorZeroImage_range] at hz
  exact hu ((OpenZero.Constructions.diagonalBaseVector_zero_iff V X j U hU hUB V.complexDimension O hi hO u).mpr hz)

theorem diagonalVectorNormalClass_Thom :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U))
      (diagonalNormal_mapsTo V X j U hU hUB O hi hO) (2 * V.complexDimension)
      (BaseVectorNormal.Constructions.Class.vectorNormalClass (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion (OpenEquations.Constructions.productOpen V X j)) U hUB V.complexDimension
        (OpenEquations.Constructions.diagonalSection V X j V.complexDimension)) = (ComplexImmersion.Constructions.diagonalOpenImmersion V U).regularThomClass := by
  have h := ConcreteCategory.congr_hom (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ)
    (𝟙 (TopCat.of U)) (BaseSectionVector.Constructions.baseSectionVector (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion (OpenEquations.Constructions.productOpen V X j)) U hUB V.complexDimension
      (OpenEquations.Constructions.diagonalSection V X j V.complexDimension))
    (diagonalNormal_mapsTo V X j U hU hUB O hi hO)
    (BaseVectorNormal.Constructions.SectionSupport.vectorZeroImage_mapsTo (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion (OpenEquations.Constructions.productOpen V X j)) U hUB V.complexDimension
      (OpenEquations.Constructions.diagonalSection V X j V.complexDimension)) (2 * V.complexDimension))
      (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass V.complexDimension)
  simp only [Category.id_comp, ConcreteCategory.comp_apply] at h
  exact h.trans (diagonalEquation_Thom V X j U hU hUB O hi hO)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.OpenNormal.Constructions
