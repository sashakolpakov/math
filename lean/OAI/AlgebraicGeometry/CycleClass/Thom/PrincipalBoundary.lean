import OAI.AlgebraicGeometry.CycleClass.Geometric.RationalLocalPurity
import OAI.AlgebraicTopology.Cohomology.Singular.Contractible
import OAI.AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport

/-! # Principal Boundary -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.PrincipalBoundary.Constructions

noncomputable section

/-!
# ThomClass: the supported class of a complex-valued function

The normalized class of the origin pulls back to a relative class supported
on the zero set of a continuous complex-valued function. The class is the
boundary of its winding class on the complement, and hence its image in
ordinary cohomology vanishes.

The complex line is represented by the project's normal-coordinate model
`Fin 1 → ℂ`, retaining its established integral orientation normalization.
No identification with an algebraic principal-divisor cycle is assumed here.
That identification requires the local multiplicity comparison with `Scheme.ord`.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open OAI.AlgebraicGeometry.CycleClass.Geometric.RationalLocalPurity.Cycles

abbrev normalComplexLine : TopCat := TopCat.of (Fin 1 → ℂ)

abbrev puncturedComplexLine : Set normalComplexLine := {0}ᶜ

/-- The genuine connecting isomorphism for the punctured complex line. -/
def lineConnectingIso :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of puncturedComplexLine) 1 ≅
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) normalComplexLine
        puncturedComplexLine 2 :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyConnectingIso (ModuleCat.of ℚ ℚ) normalComplexLine
    puncturedComplexLine 1
    (AlgebraicTopology.Cohomology.Singular.Contractible.isZero_singularCohomology_of_contractible _ _ 1 (by decide))
    (AlgebraicTopology.Cohomology.Singular.Contractible.isZero_singularCohomology_of_contractible _ _ 2 (by decide))

/-- The punctured-line class whose boundary is the oriented class of the origin. -/
def lineWindingClass :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of puncturedComplexLine) 1 :=
  lineConnectingIso.inv (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1)

theorem lineWindingClass_boundary :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyConnecting (ModuleCat.of ℚ ℚ) normalComplexLine
      puncturedComplexLine 1 lineWindingClass = Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1 :=
  lineConnectingIso.inv_hom_id_apply _

theorem lineWindingClass_ne_zero : lineWindingClass ≠ 0 := by
  intro h
  apply Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass_ne_zero 1
  rw [← lineWindingClass_boundary, h, map_zero]

/-- The complement of the function's zero set. -/
def functionNonzeroLocus {X : TopCat} (f : X ⟶ normalComplexLine) : Set X :=
  f ⁻¹' puncturedComplexLine

/-- The supported class obtained from the actual map of pairs. -/
def functionSupportedClass {X : TopCat} (f : X ⟶ normalComplexLine) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (functionNonzeroLocus f) 2 :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f
    (A := functionNonzeroLocus f) (B := puncturedComplexLine) (fun _ hx => hx) 2
    (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1)

/-- Pull the winding class back to the function's nonvanishing locus. -/
def functionWindingClass {X : TopCat} (f : X ⟶ normalComplexLine) :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (functionNonzeroLocus f)) 1 :=
  AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
    (Geometric.LocalHomology.Cycles.subspaceMap f (A := functionNonzeroLocus f) (B := puncturedComplexLine)
      (fun _ hx => hx)) 1 lineWindingClass

/-- The supported function class has a canonical primitive on its complement. -/
theorem functionWindingClass_boundary {X : TopCat} (f : X ⟶ normalComplexLine) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyConnecting (ModuleCat.of ℚ ℚ) X (functionNonzeroLocus f) 1
      (functionWindingClass f) = functionSupportedClass f := by
  have h := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyConnecting_naturality (ModuleCat.of ℚ ℚ) f
      (A := functionNonzeroLocus f) (B := puncturedComplexLine) (fun _ hx => hx) 1)
    lineWindingClass
  change AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f _ 2
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyConnecting (ModuleCat.of ℚ ℚ) normalComplexLine
        puncturedComplexLine 1 lineWindingClass) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyConnecting (ModuleCat.of ℚ ℚ) X (functionNonzeroLocus f) 1
      (functionWindingClass f) at h
  rw [lineWindingClass_boundary] at h
  exact h.symm

/-- Forgetting the zero-set support sends the function class to zero. -/
theorem functionSupportedClass_absolute_zero {X : TopCat}
    (f : X ⟶ normalComplexLine) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) X (functionNonzeroLocus f) 2
      (functionSupportedClass f) = 0 := by
  have h := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyConnecting_inclusion (ModuleCat.of ℚ ℚ) X
      (functionNonzeroLocus f) 1) (functionWindingClass f)
  change AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) X (functionNonzeroLocus f) 2
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyConnecting (ModuleCat.of ℚ ℚ) X (functionNonzeroLocus f) 1
      (functionWindingClass f)) = 0 at h
  rwa [functionWindingClass_boundary] at h

/-- These supported classes commute with actual continuous pullback. -/
theorem functionSupportedClass_pullback {X Y : TopCat}
    (g : X ⟶ Y) (f : Y ⟶ normalComplexLine) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) g
      (A := functionNonzeroLocus (g ≫ f)) (B := functionNonzeroLocus f)
      (fun _ hx => hx) 2 (functionSupportedClass f) =
      functionSupportedClass (g ≫ f) :=
  ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) g f
      (A := functionNonzeroLocus (g ≫ f)) (B := functionNonzeroLocus f)
      (C := puncturedComplexLine) (fun _ hx => hx) (fun _ hx => hx) 2)
    (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1)

/-- The identity function recovers the normalized origin class. -/
theorem functionSupportedClass_identity :
    functionSupportedClass (𝟙 normalComplexLine) = Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1 := by
  unfold functionSupportedClass
  change AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 normalComplexLine)
    (A := puncturedComplexLine) (B := puncturedComplexLine) (fun _ hx => hx) 2 _ = _
  rw [AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_id]
  rfl

end

end OAI.AlgebraicGeometry.CycleClass.Thom.PrincipalBoundary.Constructions
