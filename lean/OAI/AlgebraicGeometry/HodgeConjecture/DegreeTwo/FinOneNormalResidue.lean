import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalPairReindex
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalMultiplicity
import OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.Winding
import OAI.AlgebraicGeometry.CycleClass.Geometric.ImmersionNormalFin

/-! # Fin One Normal Residue -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.FinOneNormalResidue.Constructions

noncomputable section

/-!
# DegreeTwo: winding normalization in the canonical codimension-one model

The actual complex-line local class equals the one-coordinate class under
the actual complex-linear map. This identifies equation winding with the
normalized chart class used by the global Thom construction.
-/

open _root_.CategoryTheory
open OAI.AlgebraicGeometry.CycleClass.Geometric.ImmersionNormalFin.Cycles OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.Winding

theorem planeNormalClass_eq_coordinates :
    WindingResidue.Constructions.ExponentialCocycle.planeNormalClass = CycleClass.Geometric.ComplexLocalPurityNaturality.Cycles.complexCoordinateLocalClass NormalPairReindex.Constructions.planeCoordinates := by
  let A : ℕ → ModuleCat.{0} ℚ := fun n => CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.finiteComplexLocalCohomology ℂ (2 * n)
  have hd : Module.finrank ℂ ℂ = 1 := Module.finrank_self ℂ
  have transport (i j : ℕ) (h : i = j) (e : A i ≅ ExponentialCocycleQ.Constructions.ExponentialCocycle.Q) :
      (eqToHom (congrArg A h)) (e.inv 1) =
        ((cast (congrArg (fun n => A n ≅ ExponentialCocycleQ.Constructions.ExponentialCocycle.Q) h) e).inv 1) := by
    cases h
    rfl
  have hp : WindingResidue.Constructions.ExponentialCocycle.planeNormalClass =
      (eqToHom (congrArg A hd)) (CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.finiteComplexLocalClass ℂ) := by
    exact (transport _ _ hd (CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.finiteComplexTopCohomologyIso ℂ)).symm
  rw [hp, CycleClass.Geometric.ComplexLocalPurityNaturality.Cycles.finiteComplexLocalClass_eq_coordinate,
    CycleClass.Geometric.ComplexLocalPurityNaturality.Cycles.complexCoordinateLocalClass_cast hd (CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.finiteComplexCoordinates ℂ)]
  exact CycleClass.Geometric.ComplexLocalPurityNaturality.Cycles.complexCoordinateLocalClass_eq _ NormalPairReindex.Constructions.planeCoordinates

/-- The actual complex-linear coordinate inverse preserves the fixed
normalization in literal cohomological degree two. -/
theorem planeNormalClass_pullback_finOne :
    (CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.complexLinearLocalCohomologyIso NormalPairReindex.Constructions.planeCoordinates.symm 2).hom WindingResidue.Constructions.ExponentialCocycle.planeNormalClass =
      CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1 := by
  rw [planeNormalClass_eq_coordinates]
  have h := CycleClass.Geometric.ComplexLocalPurityNaturality.Cycles.complexCoordinateLocalClass_naturality NormalPairReindex.Constructions.planeCoordinates.symm
    (ContinuousLinearEquiv.refl ℂ (Fin 1 → ℂ)) NormalPairReindex.Constructions.planeCoordinates
  simpa only [mul_one, CycleClass.Geometric.ImmersionNormalFin.Cycles.complexCoordinateLocalClass_refl] using h

variable {M N E : Type} [TopologicalSpace N] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : M → N} {x : M} (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin 1 → ℂ) f x)

/-- An actual equation equal to the sole normal coordinate has the
canonical local Thom coefficient, also after enlarging its support. -/
theorem finOne_equation_supportedWindingClass
    (A : Set P.neighborhood) (hA : A ⊆ P.relativeComplement)
    (s : C(A, ℂ)) (hs : ∀ y, s y ≠ 0)
    (hcoord : ∀ y, s y = P.normalCoordinate y.val 0) :
    DivisorClass.Chern.Supported.Winding.supportedWindingClass (TopCat.of P.neighborhood) A s hs =
      (-WindingResidue.Constructions.ExponentialCocycle.windingNormalCoefficient) •
        AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap ExponentialCocycleQ.Constructions.ExponentialCocycle.Q (𝟙 (TopCat.of P.neighborhood)) hA 2
          P.rationalClassFin := by
  let e := (CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.complexLinearTopIso NormalPairReindex.Constructions.planeCoordinates.symm).hom
  let g : TopCat.of P.neighborhood ⟶ ExponentialCocycleQ.Constructions.ExponentialCocycle.Plane := P.normalCoordinate ≫ e
  have hg : Set.MapsTo g A ({0}ᶜ : Set ℂ) :=
    (CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.complexLinearEquiv_mapsTo_puncture NormalPairReindex.Constructions.planeCoordinates.symm).comp
      (fun _ hy => P.normalCoordinate_mapsTo (hA hy))
  let t := NormalResidue.Constructions.ExponentialCocycle.restrictedFunction g A hg
  have ht : ∀ y, t y ≠ 0 := fun y => (NormalResidue.Constructions.ExponentialCocycle.nonzeroRestriction g A hg y).property
  have hst : s = t := by
    apply ContinuousMap.ext
    intro y
    exact hcoord y
  have hmap : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap ExponentialCocycleQ.Constructions.ExponentialCocycle.Q g hg 2 =
      (CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.complexLinearLocalCohomologyIso NormalPairReindex.Constructions.planeCoordinates.symm 2).hom ≫
        P.normalCohomologyMap ExponentialCocycleQ.Constructions.ExponentialCocycle.Q 2 ≫
        AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap ExponentialCocycleQ.Constructions.ExponentialCocycle.Q (𝟙 (TopCat.of P.neighborhood)) hA 2 := by
    have he : Set.MapsTo e ({0}ᶜ : Set (Fin 1 → ℂ)) ({0}ᶜ : Set ℂ) :=
      CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.complexLinearEquiv_mapsTo_puncture NormalPairReindex.Constructions.planeCoordinates.symm
    have hn : Set.MapsTo P.normalCoordinate A ({0}ᶜ : Set (Fin 1 → ℂ)) :=
      fun _ hy => P.normalCoordinate_mapsTo (hA hy)
    have hr : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap ExponentialCocycleQ.Constructions.ExponentialCocycle.Q P.normalCoordinate hn 2 =
        P.normalCohomologyMap ExponentialCocycleQ.Constructions.ExponentialCocycle.Q 2 ≫
          AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap ExponentialCocycleQ.Constructions.ExponentialCocycle.Q (𝟙 (TopCat.of P.neighborhood)) hA 2 := by
      have h := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp ExponentialCocycleQ.Constructions.ExponentialCocycle.Q (𝟙 (TopCat.of P.neighborhood))
        P.normalCoordinate hA P.normalCoordinate_mapsTo 2
      exact h.symm
    exact (CycleClass.Geometric.RelativeCochainFunctoriality.Cohomology.relativeSingularCohomologyMap_of_comp ExponentialCocycleQ.Constructions.ExponentialCocycle.Q P.normalCoordinate e hn he 2).trans
      (congrArg (fun a => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap ExponentialCocycleQ.Constructions.ExponentialCocycle.Q e he 2 ≫ a) hr)
  have hclass : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap ExponentialCocycleQ.Constructions.ExponentialCocycle.Q g hg 2 WindingResidue.Constructions.ExponentialCocycle.planeNormalClass =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap ExponentialCocycleQ.Constructions.ExponentialCocycle.Q (𝟙 (TopCat.of P.neighborhood)) hA 2
        P.rationalClassFin := by
    rw [hmap]
    change AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap ExponentialCocycleQ.Constructions.ExponentialCocycle.Q (𝟙 (TopCat.of P.neighborhood)) hA 2
      (P.normalCohomologyMap ExponentialCocycleQ.Constructions.ExponentialCocycle.Q 2
        ((CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.complexLinearLocalCohomologyIso NormalPairReindex.Constructions.planeCoordinates.symm 2).hom WindingResidue.Constructions.ExponentialCocycle.planeNormalClass)) = _
    rw [planeNormalClass_pullback_finOne, P.rationalClassFin_eq_normalPullback]
  calc
    _ = DivisorClass.Chern.Supported.Winding.supportedWindingClass (TopCat.of P.neighborhood) A t ht :=
      DivisorClass.Chern.Supported.Winding.supportedWindingClass_congr _ _ s t hs ht hst
    _ = - (WindingResidue.Constructions.ExponentialCocycle.windingNormalCoefficient •
        AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap ExponentialCocycleQ.Constructions.ExponentialCocycle.Q g hg 2 WindingResidue.Constructions.ExponentialCocycle.planeNormalClass) := by
      rw [DivisorClass.Chern.Supported.Winding.supportedWindingClass_logarithmic]
      exact congrArg Neg.neg (NormalResidue.Constructions.ExponentialCocycle.restrictedFunction_residue_eq_smul g A hg)
    _ = _ := by rw [hclass, neg_smul]

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.FinOneNormalResidue.Constructions
