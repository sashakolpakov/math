import OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.SerreClassFormula
import OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Cup
import OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Gysin

/-! # Local Serre Cancellation -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.LocalSerreCancellation.Constructions

noncomputable section

/-! Cancel the genuine supported diagonal Thom isomorphism in the
actual local Serre formula on a specified etale coordinate chart. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped MonoidalCategory TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Ambient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.LocalIsolation.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.SerreClassFormula.Constructions.Chart OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Cup.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.OpenEquations.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.OpenVector.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.ComplexImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Gysin.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ImmersionOpenRestriction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen
open OAI.AlgebraicGeometry.CycleClass.Thom.EtaleSectionVector.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Section.VectorHeadChange.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions.Map OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.VectorPresentationTarget.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.GysinDegree.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p q : ℕ)
  (A : Geometric.DimensionCycles.DimensionCycleSupport V p) (B : Geometric.DimensionCycles.DimensionCycleSupport V q) (Z : Geometric.DimensionCycles.DimensionCycleSupport V (p + q))
  (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (j : X ⟶ V.toOver)
  [IsAffine X.left] [IsIntegral X.left] [Smooth X.hom] [IsOpenImmersion j.left]
  [Algebra (MvPolynomial (Fin V.complexDimension) ℂ) Γ(X.left, ⊤)]
  [IsScalarTower ℂ (MvPolynomial (Fin V.complexDimension) ℂ) Γ(X.left, ⊤)]
  [Algebra.IsStandardEtale (MvPolynomial (Fin V.complexDimension) ℂ) Γ(X.left, ⊤)]

local instance : IsIntegral (X ⊗ X).left := Affine.ProductIs.Constructions.affineProduct_isIntegral X X
local instance : Smooth (X ⊗ X).hom := inferInstanceAs (Smooth (pullback.fst X.hom X.hom ≫ X.hom))
local instance : IsIntegral (Ambient.Constructions.productVariety V V).toOver.left := (Ambient.Constructions.productVariety V V).property
local instance : Smooth (Ambient.Constructions.productVariety V V).toOver.hom := (Ambient.Constructions.productVariety V V).presentation.smooth
local instance : Nonempty (OpenEquations.Constructions.productOpen V X j) :=
  ⟨⟨OpenEquations.Constructions.center V X j (genericPoint X.left), OpenEquations.Constructions.center_mem V X j (genericPoint X.left)⟩⟩

theorem exists_chart_serre_pullback_formula (hpos : 0 < V.complexDimension)
    (hxA : IntersectionGeometry.supportPoint Z.val ∈ (A.val : Set V.carrier))
    (hxB : IntersectionGeometry.supportPoint Z.val ∈ (B.val : Set V.carrier))
    (hproper : ∀ C : IrreducibleCloseds V.carrier,
      (C : Set V.carrier) ⊆ (A.val : Set V.carrier) ∩ (B.val : Set V.carrier) → p + q ≤ Geometric.DimensionCycles.dimensionCodimension V C)
    (y : X.left) (hy : j.left y = Z.genericPoint) :
    ∃ W : (Ambient.Constructions.productVariety V V).carrier.Opens, W ≤ OpenEquations.Constructions.productOpen V X j ∧
      (Ambient.Constructions.diagonalSupport V (p + q) Z).genericPoint ∈ W ∧
      ∀ (U : Opens (Ambient.Constructions.productVariety V V).analyticSpace)
        (_hUW : (U : Set (Ambient.Constructions.productVariety V V).analyticSpace) ⊆ Scheme.SectionEvaluation.Constructions.analyticOpen (Ambient.Constructions.productVariety V V).toOver W)
        (hUP : (U : Set (Ambient.Constructions.productVariety V V).analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (OpenVector.Constructions.productOpenOverMap V X j)))
        (_hUB : (U : Set (Ambient.Constructions.productVariety V V).analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion (OpenEquations.Constructions.productOpen V X j))))
        (_hUR : (U : Set (Ambient.Constructions.productVariety V V).analyticSpace) ⊆ (Ambient.Constructions.diagonalSupport V (p + q) Z).regularAmbientOpen)
        (O : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
        (_hi : Set.InjOn (Section.VectorHeadChange.Constructions.sectionVectorEquation X V.complexDimension (EtaleSectionVector.Constructions.coordinateSections X V.complexDimension)) O)
        (_hO : ∀ u : U, (Scheme.PointProduct.Constructions.schemePointProductHomeomorph X X
            (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift (OpenVector.Constructions.productOpenOverMap V X j) U hUP u)).1 ∈ O ∧
          (Scheme.PointProduct.Constructions.schemePointProductHomeomorph X X
            (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift (OpenVector.Constructions.productOpenOverMap V X j) U hUP u)).2 ∈ O)
        {L : Type} (u : L → U) (_hu : IsOpen (Set.range u)ᶜ)
        (_hC : (Subtype.val : U → (Ambient.Constructions.productVariety V V).analyticSpace) ⁻¹'
          Set.range (LocalIsolation.Constructions.pairedSupport V p q A B).analyticInclusion ⊆ Set.range u)
        (_hZ : (Subtype.val : U → (Ambient.Constructions.productVariety V V).analyticSpace) ⁻¹'
          Set.range (Ambient.Constructions.diagonalSupport V (p + q) Z).analyticInclusion ⊆ Set.range u),
        AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (ComplexImmersion.Constructions.diagonalOpenImmersion V U).regularComplementTopCatMap
          (A := (ComplexImmersion.Constructions.diagonalOpenImmersion V U).regularComplementInclusion ⁻¹' (Set.range u)ᶜ) (B := (Set.range u)ᶜ)
          (fun _ hx => hx) (2 * (p + q))
          (Open.SupportedLift.Constructions.Map.relativeClassMap (Ambient.Constructions.productVariety V V) U (Set.range u) (p + q)
            (Open.SupportedLift.Constructions.restrictCycle (Ambient.Constructions.productVariety V V) U (Set.range u) (p + q) (Finsupp.single (LocalIsolation.Constructions.pairedSupport V p q A B) 1))) =
        Open.SupportedLift.Constructions.Map.relativeClassMap V (Closed.ImmersionOpenRestriction.Constructions.sourceOpen (ComplexImmersion.Constructions.diagonalImmersion V) U)
          ((ComplexImmersion.Constructions.diagonalOpenImmersion V U).regularComplementInclusion ⁻¹' Set.range u) (p + q)
          (Open.SupportedLift.Constructions.restrictCycle V (Closed.ImmersionOpenRestriction.Constructions.sourceOpen (ComplexImmersion.Constructions.diagonalImmersion V) U)
            ((ComplexImmersion.Constructions.diagonalOpenImmersion V U).regularComplementInclusion ⁻¹' Set.range u) (p + q)
            (Finsupp.single Z (IntersectionGeometry.intersectionMultiplicity V.presentation A.val B.val Z.val))) := by
  classical
  obtain ⟨W, hWP, hxW, hf⟩ := SerreClassFormula.Constructions.Chart.exists_chart_serre_formula V p q A B Z X j hpos hxA hxB hproper y hy
  refine ⟨W, hWP, hxW, ?_⟩
  intro U hUW hUP hUB hUR O hi hO L u hu hC hZ
  let D := ComplexImmersion.Constructions.diagonalOpenImmersion V U
  obtain ⟨a, ha⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of U)
    (Set.range D.regularComplementInclusion)ᶜ) (2 * V.complexDimension) D.regularThomClass
  let g := Intersection.GysinDegree.Constructions.intersectionGysinAt D a ha u hu ((p + q) + V.complexDimension) (Nat.add_comm _ _)
  apply g.toLinearEquiv.injective
  have hl := hf U hUW hUB u hu (by
    intro C hne
    have he : C = LocalIsolation.Constructions.pairedSupport V p q A B := by
      by_contra hn
      exact hne (Finsupp.single_eq_of_ne hn)
    subst C
    exact hC)
  have h := congrArg (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U))
    (Cup.Constructions.diagonalCup_mapsTo V X j U hUP hUB O hi hO u) (2 * ((p + q) + V.complexDimension))) hl
  rw [Cup.Constructions.cycleVectorClass_diagonalGysin V X j U hUP hUB O hi hO u hu (p + q)
    (Finsupp.single (LocalIsolation.Constructions.pairedSupport V p q A B) 1) a ha] at h
  have ht := Cycle.VectorPresentationTarget.Constructions.presentTo_cycleClass (Ambient.Constructions.productVariety V V) (OpenEquations.Constructions.productOpen V X j) U hUB u V.complexDimension
    (OpenEquations.Constructions.diagonalSection V X j V.complexDimension) (Set.range u) (Set.range D.regularComplementInclusion)
    (Set.range D.regularComplementInclusion ∩ Set.range u) rfl
    (Cup.Constructions.diagonalVector_range_eq V X j U hUP hUB O hi hO) (Set.inter_comm _ _)
    ((p + q) + V.complexDimension)
    (Finsupp.single (Ambient.Constructions.diagonalSupport V (p + q) Z) (IntersectionGeometry.intersectionMultiplicity V.presentation A.val B.val Z.val))
  exact h.trans (ht.trans (Gysin.Constructions.diagonalGysin_singleCycle V (p + q) Z U hUR u hZ hu a ha
    (IntersectionGeometry.intersectionMultiplicity V.presentation A.val B.val Z.val)).symm)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.LocalSerreCancellation.Constructions
