import OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.OpenNormal
import OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.VectorPresentationTarget
import OAI.AlgebraicGeometry.CycleClass.Thom.Supported.CupCommutativity
import OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.GysinDegree

/-! # Cup -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Cup.Constructions

noncomputable section

/-! The actual local cycle-vector class for the diagonal equations is
the diagonal Thom pushforward of the restricted original class. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped MonoidalCategory TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Ambient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.OpenVector.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.OpenEquations.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.ComplexImmersion.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.OpenZero.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.OpenNormal.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic
open OAI.AlgebraicGeometry.CycleClass.Thom.BaseVectorNormal.Constructions.SectionSupport OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.EtaleSectionVector.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Section.VectorHeadChange.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.Vector.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.VectorPresentationTarget.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.EvenIntersectionAssociativity.Constructions.SupportedCupTargets OAI.AlgebraicGeometry.CycleClass.Thom.Supported.CupCommutativity.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions.Map OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.GysinDegree.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.Normal

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
  [Algebra (MvPolynomial (Fin V.complexDimension) ℂ) Γ(X.left, ⊤)]
  [IsScalarTower ℂ (MvPolynomial (Fin V.complexDimension) ℂ) Γ(X.left, ⊤)]
  (O : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
  (hi : Set.InjOn (Section.VectorHeadChange.Constructions.sectionVectorEquation X V.complexDimension (EtaleSectionVector.Constructions.coordinateSections X V.complexDimension)) O)
  (hO : ∀ u : U, (Scheme.PointProduct.Constructions.schemePointProductHomeomorph X X
      (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift (OpenVector.Constructions.productOpenOverMap V X j) U hU u)).1 ∈ O ∧
    (Scheme.PointProduct.Constructions.schemePointProductHomeomorph X X
      (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift (OpenVector.Constructions.productOpenOverMap V X j) U hU u)).2 ∈ O)

local notation "D" => OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.ComplexImmersion.Constructions.diagonalOpenImmersion V U

include hi hO in
theorem diagonalVector_range_eq :
    Set.range (BaseVectorNormal.Constructions.SectionSupport.vectorZeroImage (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion (OpenEquations.Constructions.productOpen V X j)) U hUB V.complexDimension
      (OpenEquations.Constructions.diagonalSection V X j V.complexDimension)) = Set.range (D).regularComplementInclusion := by
  ext u
  rw [BaseVectorNormal.Constructions.SectionSupport.vectorZeroImage_range]
  exact (OpenZero.Constructions.diagonalBaseVector_zero_iff V X j U hU hUB V.complexDimension O hi hO u).symm

variable {L : Type} (u : L → U) (hu : IsOpen (Set.range u)ᶜ)

include hi hO in
theorem diagonalCup_mapsTo : Set.MapsTo (𝟙 (TopCat.of U))
    (Set.range (D).regularComplementInclusion ∩ Set.range u)ᶜ
    (Cycle.Vector.Constructions.Class.vectorIntersectionSupport (Ambient.Constructions.productVariety V V) (OpenEquations.Constructions.productOpen V X j) U hUB u V.complexDimension
      (OpenEquations.Constructions.diagonalSection V X j V.complexDimension))ᶜ :=
  Cycle.VectorPresentationTarget.Constructions.presentTo_mapsTo (Ambient.Constructions.productVariety V V) (OpenEquations.Constructions.productOpen V X j) U hUB u V.complexDimension
    (OpenEquations.Constructions.diagonalSection V X j V.complexDimension) (Set.range u) (Set.range (D).regularComplementInclusion)
    (Set.range (D).regularComplementInclusion ∩ Set.range u) rfl
    (diagonalVector_range_eq V X j U hU hUB O hi hO) (Set.inter_comm _ _)

variable [Algebra.FormallyEtale (MvPolynomial (Fin V.complexDimension) ℂ) Γ(X.left, ⊤)]
  (p : ℕ) (c : Geometric.DimensionCycles.RationalDimensionCycle (Ambient.Constructions.productVariety V V) p)

theorem cycleVectorClass_diagonalThom :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U))
      (diagonalCup_mapsTo V X j U hU hUB O hi hO u) (2 * (p + V.complexDimension))
      (Cycle.Vector.Constructions.Class.cycleVectorClassAt (Ambient.Constructions.productVariety V V) (OpenEquations.Constructions.productOpen V X j) U hUB u p V.complexDimension
        (p + V.complexDimension) rfl (OpenEquations.Constructions.diagonalSection V X j V.complexDimension) hu c) =
    EvenIntersectionAssociativity.Constructions.SupportedCupTargets.cupTo (TopCat.of U) (Set.range (D).regularComplementInclusion)ᶜ (Set.range u)ᶜ
      (Set.range (D).regularComplementInclusion ∩ Set.range u)ᶜ (D).closed.isClosed_range.isOpen_compl hu
      (ImageIntersectionTo.Constructions.Normal.intersectionComplement_eq (D).regularComplementInclusion u)
      (2 * V.complexDimension) (2 * p) (2 * (p + V.complexDimension)) (by omega)
      (D).regularThomClass
      (Open.SupportedLift.Constructions.Map.relativeClassMap (Ambient.Constructions.productVariety V V) U (Set.range u) p
        (Open.SupportedLift.Constructions.restrictCycle (Ambient.Constructions.productVariety V V) U (Set.range u) p c)) := by
  have h := Cycle.VectorPresentationTarget.Constructions.presentTo_cycleVectorClass (Ambient.Constructions.productVariety V V) (OpenEquations.Constructions.productOpen V X j) U hUB u V.complexDimension
    (OpenEquations.Constructions.diagonalSection V X j V.complexDimension) (Set.range u) (Set.range (D).regularComplementInclusion)
    (Set.range (D).regularComplementInclusion ∩ Set.range u) rfl
    (diagonalVector_range_eq V X j U hU hUB O hi hO) (Set.inter_comm _ _)
    p (p + V.complexDimension) rfl hu hu (D).closed.isClosed_range.isOpen_compl
    ((ImageIntersectionTo.Constructions.Normal.intersectionComplement_eq u (D).regularComplementInclusion).trans (congrArg Set.compl (Set.inter_comm _ _)))
    (OpenNormal.Constructions.diagonalEquation_mapsTo V X j U hU hUB O hi hO) c
  rw [OpenNormal.Constructions.diagonalEquation_Thom V X j U hU hUB O hi hO] at h
  exact h.trans (Supported.CupCommutativity.Constructions.cupTo_even_comm _ _ _ _ _ _ _ _ p (2 * V.complexDimension) _ (by omega) (by omega) _ _)

variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of U)
    (Set.range (ComplexImmersion.Constructions.diagonalOpenImmersion V U).regularComplementInclusion)ᶜ) (2 * V.complexDimension))
  (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * V.complexDimension) a = (ComplexImmersion.Constructions.diagonalOpenImmersion V U).regularThomClass)

theorem cycleVectorClass_diagonalGysin :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U))
      (diagonalCup_mapsTo V X j U hU hUB O hi hO u) (2 * (p + V.complexDimension))
      (Cycle.Vector.Constructions.Class.cycleVectorClassAt (Ambient.Constructions.productVariety V V) (OpenEquations.Constructions.productOpen V X j) U hUB u p V.complexDimension
        (p + V.complexDimension) rfl (OpenEquations.Constructions.diagonalSection V X j V.complexDimension) hu c) =
    (Intersection.GysinDegree.Constructions.intersectionGysinAt (D) a ha u hu (p + V.complexDimension) (Nat.add_comm _ _)).hom
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (D).regularComplementTopCatMap
        (A := (D).regularComplementInclusion ⁻¹' (Set.range u)ᶜ) (B := (Set.range u)ᶜ)
        (fun _ hx => hx) (2 * p)
        (Open.SupportedLift.Constructions.Map.relativeClassMap (Ambient.Constructions.productVariety V V) U (Set.range u) p
          (Open.SupportedLift.Constructions.restrictCycle (Ambient.Constructions.productVariety V V) U (Set.range u) p c))) :=
  (cycleVectorClass_diagonalThom V X j U hU hUB O hi hO u hu p c).trans
    (Intersection.GysinDegree.Constructions.cupTo_eq_gysinAt_pullback (D) a ha u hu (p + V.complexDimension) (Nat.add_comm _ _) _)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Cup.Constructions
