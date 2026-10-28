import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.BaseTangentObstruction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.Closed

/-! # Primitives -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyTangent.Primitives

noncomputable section

section

/-! Vanishing of a native tangent class supplies literal scalar
primitives in the fixed-fiber coefficient rings on the original affine
cover, with the exact transition sign. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

variable (R : Type) [CommRing R] [Algebra ℂ R] [Algebra R ℂ] [IsScalarTower ℂ R ℂ]
    (X : Over (Spec (.of R))) [Smooth X.hom] [IsSeparated X.hom]
    [IsIntegral (TangentBasePoint.fixedFamilyFiber ℂ R X).left] [Smooth (TangentBasePoint.fixedFamilyFiber ℂ R X).hom]
    [GrpObj (TangentBasePoint.fixedFamilyFiber ℂ R X)] (U : X.left.AffineOpenCover)

attribute [local implicit_reducible] Family.AffineCoverIntersections.familyCoverAffineOpen Family.AffineCoverIntersections.familyCoverPairAffineOpen
attribute [local implicit_reducible] Fixed.CechCover.fixedFamilyCechCover TangentBasePoint.fixedFamilyFiber FixedFiber.CoordinateProjection.fixedFiberAffineOpen
attribute [local irreducible] FixedFiber.RegularSections.fixedFiberRegularSectionEquiv

abbrev fixedFamilyScalarGauges := ∀ i : U.I₀, ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R X (Family.AffineCoverIntersections.familyCoverAffineOpen R X U i)

def IsFamilyTangentScalarPrimitive (d : Derivation ℂ R ℂ)
    (z : Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R X)) (a : fixedFamilyScalarGauges R X U) : Prop :=
  ∀ i j : U.I₀, ConormalCocycle.familyTangentConormalPair R X U i j d z =
    FixedFiber.DerivationPresheaf.fixedFiberTensorRestriction R ℂ X
      (show (Family.AffineCoverIntersections.familyCoverPairAffineOpen R X U i j).1 ≤ (Family.AffineCoverIntersections.familyCoverAffineOpen R X U i).1 from inf_le_left) (a i) -
    FixedFiber.DerivationPresheaf.fixedFiberTensorRestriction R ℂ X
      (show (Family.AffineCoverIntersections.familyCoverPairAffineOpen R X U i j).1 ≤ (Family.AffineCoverIntersections.familyCoverAffineOpen R X U j).1 from inf_le_right) (a j)

theorem familyTangentScalarPrimitive_of_class_zero (d : Derivation ℂ R ℂ)
    (z : Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R X)) (hz : Family.BaseTangentObstruction.familyTangentSheafClass R X U d z = 0) :
    ∃ a : fixedFamilyScalarGauges R X U, IsFamilyTangentScalarPrimitive R X U d z a := by
  obtain ⟨s, hs⟩ := RegularPair.Closed.regularPairPrimitive_of_sheafClass_zero (TangentBasePoint.fixedFamilyFiber ℂ R X).left
    (Fixed.CechCover.fixedFamilyCechCover ℂ R X U) (RegularCocycle.familyTangentRegularPair R X U d z)
    (Fixed.CechCover.fixedFamilyCechCover_covers ℂ R X U) (RegularCocycle.familyTangentRegularPair_cocycle R X U d z) hz
  let a : fixedFamilyScalarGauges R X U := fun i =>
    (FixedFiber.RegularSections.fixedFiberRegularSectionEquiv R ℂ X (Family.AffineCoverIntersections.familyCoverAffineOpen R X U i)).symm (s i)
  have he (i : U.I₀) : FixedFiber.RegularSections.fixedFiberRegularSectionEquiv R ℂ X (Family.AffineCoverIntersections.familyCoverAffineOpen R X U i) (a i) = s i :=
    (FixedFiber.RegularSections.fixedFiberRegularSectionEquiv R ℂ X (Family.AffineCoverIntersections.familyCoverAffineOpen R X U i)).apply_symm_apply (s i)
  refine ⟨a, fun i j => ?_⟩
  apply (FixedFiber.RegularSections.fixedFiberRegularSectionEquiv R ℂ X (Family.AffineCoverIntersections.familyCoverPairAffineOpen R X U i j)).injective
  rw [map_sub, FixedFiber.RegularSections.fixedFiberRegularSectionEquiv_restrict, FixedFiber.RegularSections.fixedFiberRegularSectionEquiv_restrict, he, he]
  exact hs i j

end

section

/-! Scalar primitives for the native tangent classes assemble on a
basis into actual conormal-valued correction terms on the original cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

variable (R : Type) [CommRing R] [Algebra ℂ R] [Algebra R ℂ] [IsScalarTower ℂ R ℂ]
    (X : Over (Spec (.of R))) [Smooth X.hom] [IsSeparated X.hom]
    [IsIntegral (TangentBasePoint.fixedFamilyFiber ℂ R X).left] [Smooth (TangentBasePoint.fixedFamilyFiber ℂ R X).hom]
    [GrpObj (TangentBasePoint.fixedFamilyFiber ℂ R X)] (U : X.left.AffineOpenCover)

attribute [local implicit_reducible] Family.AffineCoverIntersections.familyCoverAffineOpen Family.AffineCoverIntersections.familyCoverPairAffineOpen

abbrev fixedFamilyConormalGauges := ∀ i : U.I₀,
  Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R X) →ₗ[ℂ]
    ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R X (Family.AffineCoverIntersections.familyCoverAffineOpen R X U i)

def IsFamilyTangentConormalPrimitive (d : Derivation ℂ R ℂ) (v : fixedFamilyConormalGauges R X U) : Prop :=
  ∀ i j : U.I₀, ∀ z : Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R X),
    ConormalCocycle.familyTangentConormalPair R X U i j d z =
      FixedFiber.DerivationPresheaf.fixedFiberTensorRestriction R ℂ X
        (show (Family.AffineCoverIntersections.familyCoverPairAffineOpen R X U i j).1 ≤ (Family.AffineCoverIntersections.familyCoverAffineOpen R X U i).1 from inf_le_left) (v i z) -
      FixedFiber.DerivationPresheaf.fixedFiberTensorRestriction R ℂ X
        (show (Family.AffineCoverIntersections.familyCoverPairAffineOpen R X U i j).1 ≤ (Family.AffineCoverIntersections.familyCoverAffineOpen R X U j).1 from inf_le_right) (v j z)

theorem familyTangentConormalPrimitive_of_classes_zero (d : Derivation ℂ R ℂ)
    (hz : ∀ z : Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R X), Family.BaseTangentObstruction.familyTangentSheafClass R X U d z = 0) :
    ∃ v : fixedFamilyConormalGauges R X U, IsFamilyTangentConormalPrimitive R X U d v := by
  let b := Module.Free.chooseBasis ℂ (Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R X))
  have h : ∀ t, ∃ a : fixedFamilyScalarGauges R X U, IsFamilyTangentScalarPrimitive R X U d (b t) a :=
    fun t => familyTangentScalarPrimitive_of_class_zero R X U d (b t) (hz (b t))
  choose a ha using h
  let v : fixedFamilyConormalGauges R X U := fun i => b.constr ℂ (fun t => a t i)
  refine ⟨v, fun i j z => ?_⟩
  have hv : ConormalCocycle.familyTangentConormalPair R X U i j d =
      (FixedFiber.DerivationPresheaf.fixedFiberTensorRestriction R ℂ X
        (show (Family.AffineCoverIntersections.familyCoverPairAffineOpen R X U i j).1 ≤ (Family.AffineCoverIntersections.familyCoverAffineOpen R X U i).1 from inf_le_left)).toLinearMap.comp (v i) -
      (FixedFiber.DerivationPresheaf.fixedFiberTensorRestriction R ℂ X
        (show (Family.AffineCoverIntersections.familyCoverPairAffineOpen R X U i j).1 ≤ (Family.AffineCoverIntersections.familyCoverAffineOpen R X U j).1 from inf_le_right)).toLinearMap.comp (v j) := by
    apply b.ext
    intro t
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      v, Module.Basis.constr_basis]
    exact ha t i j
  exact LinearMap.congr_fun hv z

end

/-! Vanishing of the native base-tangent obstruction constructs
actual derivation correction terms on the original affine cover. Their
restricted differences are the actual linear transition derivations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

variable (R : Type) [CommRing R] [Algebra ℂ R] [Algebra R ℂ] [IsScalarTower ℂ R ℂ]
    (X : Over (Spec (.of R))) [Smooth X.hom] [IsSeparated X.hom]
    [IsIntegral (TangentBasePoint.fixedFamilyFiber ℂ R X).left] [Smooth (TangentBasePoint.fixedFamilyFiber ℂ R X).hom]
    [GrpObj (TangentBasePoint.fixedFamilyFiber ℂ R X)] (U : X.left.AffineOpenCover)

attribute [local implicit_reducible] Family.AffineCoverIntersections.familyCoverAffineOpen Family.AffineCoverIntersections.familyCoverPairAffineOpen
attribute [local irreducible] FixedFiber.AffineCoefficient.fixedFiberConormalLinearEquiv

local instance familyPrimitiveH1_complexModule :
    Module ℂ (SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule (TangentBasePoint.fixedFamilyFiber ℂ R X).left) 1) :=
  StructureComplexScalars.structureH1ComplexModule (TangentBasePoint.fixedFamilyFiber ℂ R X)

abbrev fixedFamilyDerivationGauges := ∀ i : U.I₀,
  Derivation ℂ (ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R X (Family.AffineCoverIntersections.familyCoverAffineOpen R X U i))
    (ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R X (Family.AffineCoverIntersections.familyCoverAffineOpen R X U i))

def IsFamilyTangentDerivationPrimitive (d : Derivation ℂ R ℂ) (a : fixedFamilyDerivationGauges R X U) : Prop :=
  ∀ i j : U.I₀, CechCycle.familyTangentPair ℂ R X U i j d =
    FixedFiber.DerivationPresheaf.fixedFiberDerivationRestriction R ℂ X
      (show (Family.AffineCoverIntersections.familyCoverPairAffineOpen R X U i j).1 ≤ (Family.AffineCoverIntersections.familyCoverAffineOpen R X U i).1 from inf_le_left) (a i) -
    FixedFiber.DerivationPresheaf.fixedFiberDerivationRestriction R ℂ X
      (show (Family.AffineCoverIntersections.familyCoverPairAffineOpen R X U i j).1 ≤ (Family.AffineCoverIntersections.familyCoverAffineOpen R X U j).1 from inf_le_right) (a j)

theorem familyTangentDerivationPrimitive_of_conormal (d : Derivation ℂ R ℂ)
    (v : fixedFamilyConormalGauges R X U) (hv : IsFamilyTangentConormalPrimitive R X U d v) :
    ∃ a : fixedFamilyDerivationGauges R X U, IsFamilyTangentDerivationPrimitive R X U d a := by
  let a : fixedFamilyDerivationGauges R X U := fun i =>
    (FixedFiber.AffineCoefficient.fixedFiberConormalLinearEquiv R X (Family.AffineCoverIntersections.familyCoverAffineOpen R X U i)).symm (v i)
  have he (i : U.I₀) : FixedFiber.AffineCoefficient.fixedFiberConormalLinearEquiv R X (Family.AffineCoverIntersections.familyCoverAffineOpen R X U i) (a i) = v i :=
    (FixedFiber.AffineCoefficient.fixedFiberConormalLinearEquiv R X (Family.AffineCoverIntersections.familyCoverAffineOpen R X U i)).apply_symm_apply (v i)
  refine ⟨a, fun i j => ?_⟩
  apply (FixedFiber.AffineCoefficient.fixedFiberConormalLinearEquiv R X (Family.AffineCoverIntersections.familyCoverPairAffineOpen R X U i j)).injective
  apply LinearMap.ext
  intro z
  rw [map_sub, LinearMap.sub_apply, FixedFiber.AffineCoefficient.fixedFiberConormalLinearEquiv_natural,
    FixedFiber.AffineCoefficient.fixedFiberConormalLinearEquiv_natural, he, he]
  exact hv i j z

theorem familyTangentDerivationPrimitive_of_obstruction_zero (d : Derivation ℂ R ℂ)
    (h : Family.BaseTangentObstruction.familyBaseTangentObstruction R X U d = 0) :
    ∃ a : fixedFamilyDerivationGauges R X U, IsFamilyTangentDerivationPrimitive R X U d a := by
  obtain ⟨v, hv⟩ := familyTangentConormalPrimitive_of_classes_zero R X U d
    (fun z => LinearMap.congr_fun h z)
  exact familyTangentDerivationPrimitive_of_conormal R X U d v hv

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyTangent.Primitives
