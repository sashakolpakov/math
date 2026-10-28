import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyTangent.Primitives
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.ClassZeroCriterion

/-! # Primitive Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyTangent.PrimitiveCriterion

noncomputable section

/-! The native base-tangent obstruction vanishes exactly when its
actual transition derivations are the differences of correction terms
on the original affine cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

variable (R : Type) [CommRing R] [Algebra ℂ R] [Algebra R ℂ] [IsScalarTower ℂ R ℂ]
    (X : Over (Spec (.of R))) [Smooth X.hom] [IsSeparated X.hom]
    [IsIntegral (TangentBasePoint.fixedFamilyFiber ℂ R X).left] [Smooth (TangentBasePoint.fixedFamilyFiber ℂ R X).hom]
    [GrpObj (TangentBasePoint.fixedFamilyFiber ℂ R X)] (U : X.left.AffineOpenCover)

attribute [local implicit_reducible] Family.AffineCoverIntersections.familyCoverAffineOpen Family.AffineCoverIntersections.familyCoverPairAffineOpen
attribute [local implicit_reducible] Fixed.CechCover.fixedFamilyCechCover TangentBasePoint.fixedFamilyFiber FixedFiber.CoordinateProjection.fixedFiberAffineOpen
attribute [local irreducible] FixedFiber.AffineCoefficient.fixedFiberConormalLinearEquiv FixedFiber.RegularSections.fixedFiberRegularSectionEquiv

local instance familyCriterionH1_complexModule :
    Module ℂ (SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule (TangentBasePoint.fixedFamilyFiber ℂ R X).left) 1) :=
  StructureComplexScalars.structureH1ComplexModule (TangentBasePoint.fixedFamilyFiber ℂ R X)

theorem familyTangentConormalPrimitive_of_derivation (d : Derivation ℂ R ℂ)
    (a : Primitives.fixedFamilyDerivationGauges R X U) (ha : Primitives.IsFamilyTangentDerivationPrimitive R X U d a) :
    Primitives.IsFamilyTangentConormalPrimitive R X U d
      (fun i => FixedFiber.AffineCoefficient.fixedFiberConormalLinearEquiv R X (Family.AffineCoverIntersections.familyCoverAffineOpen R X U i) (a i)) := by
  intro i j z
  have h := congrArg (fun v => FixedFiber.AffineCoefficient.fixedFiberConormalLinearEquiv R X (Family.AffineCoverIntersections.familyCoverPairAffineOpen R X U i j) v z)
    (ha i j)
  rw [map_sub, LinearMap.sub_apply, FixedFiber.AffineCoefficient.fixedFiberConormalLinearEquiv_natural,
    FixedFiber.AffineCoefficient.fixedFiberConormalLinearEquiv_natural] at h
  exact h

theorem familyTangentSheafClass_zero_of_conormalPrimitive (d : Derivation ℂ R ℂ)
    (v : Primitives.fixedFamilyConormalGauges R X U) (hv : Primitives.IsFamilyTangentConormalPrimitive R X U d v)
    (z : Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R X)) : Family.BaseTangentObstruction.familyTangentSheafClass R X U d z = 0 := by
  apply (RegularPair.ClassZeroCriterion.regularPairSheafClass_eq_zero_iff_primitive (TangentBasePoint.fixedFamilyFiber ℂ R X).left
    (Fixed.CechCover.fixedFamilyCechCover ℂ R X U) (RegularCocycle.familyTangentRegularPair R X U d z)
    (Fixed.CechCover.fixedFamilyCechCover_covers ℂ R X U) (RegularCocycle.familyTangentRegularPair_cocycle R X U d z)).mpr
  refine ⟨fun i => FixedFiber.RegularSections.fixedFiberRegularSectionEquiv R ℂ X (Family.AffineCoverIntersections.familyCoverAffineOpen R X U i) (v i z), ?_⟩
  intro i j
  have h := congrArg (FixedFiber.RegularSections.fixedFiberRegularSectionEquiv R ℂ X (Family.AffineCoverIntersections.familyCoverPairAffineOpen R X U i j)) (hv i j z)
  rw [map_sub, FixedFiber.RegularSections.fixedFiberRegularSectionEquiv_restrict, FixedFiber.RegularSections.fixedFiberRegularSectionEquiv_restrict] at h
  exact h

theorem familyBaseTangentObstruction_zero_iff_primitive (d : Derivation ℂ R ℂ) :
    Family.BaseTangentObstruction.familyBaseTangentObstruction R X U d = 0 ↔
      ∃ a : Primitives.fixedFamilyDerivationGauges R X U, Primitives.IsFamilyTangentDerivationPrimitive R X U d a := by
  constructor
  · exact Primitives.familyTangentDerivationPrimitive_of_obstruction_zero R X U d
  · rintro ⟨a, ha⟩
    apply LinearMap.ext
    intro z
    exact familyTangentSheafClass_zero_of_conormalPrimitive R X U d _
      (familyTangentConormalPrimitive_of_derivation R X U d a ha) z

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyTangent.PrimitiveCriterion
