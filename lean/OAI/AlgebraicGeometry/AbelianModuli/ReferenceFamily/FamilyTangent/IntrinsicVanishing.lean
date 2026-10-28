import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyTangent.ObstructionProduct
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.Tangent

/-! # Intrinsic Vanishing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyTangent.IntrinsicVanishing

noncomputable section

/-! For an actual abelian family, vanishing of the constructed
linear base-tangent obstruction implies vanishing of the intrinsic
native deformation obstruction on every affine cover of its tangent
family. The implication passes through the constructed global product. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable (R : Type) [CommRing R] [Algebra ℂ R] [Algebra R ℂ] [IsScalarTower ℂ R ℂ]
    (X : Over (Spec (.of R))) [GrpObj X] [IsCommMonObj X]
    [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]

attribute [local implicit_reducible] TangentBasePoint.tangentFamily TangentBasePoint.fixedFamilyFiber
attribute [local instance] Abelian.Tangent.abelianFamilyFixedFiber_smooth Abelian.Tangent.abelianFamilyFixedFiber_proper
  Abelian.Tangent.abelianFamilyFixedFiber_connected Abelian.Tangent.abelianFamilyFixedFiber_integral
  Abelian.Tangent.abelianFamilyTangent_smooth Abelian.Tangent.abelianFamilyTangent_proper Abelian.Tangent.abelianFamilyTangent_connected
  Abelian.DualObstructionCriterion.abelianDualFiber_smooth Abelian.DualObstructionCriterion.abelianDualFiber_proper Abelian.DualObstructionCriterion.abelianDualFiber_connected Abelian.DualObstructionCriterion.abelianDualFiber_integral
  Abelian.DualObstructionCriterion.abelianDualH1_complexModule

local instance familyNativeFixedFiber_group : GrpObj (TangentBasePoint.fixedFamilyFiber ℂ R X) :=
  inferInstanceAs (GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).obj X))

local instance familyNativeTangent_group (d : Derivation ℂ R ℂ) : GrpObj (TangentBasePoint.tangentFamily ℂ R X d) :=
  inferInstanceAs (GrpObj ((Over.pullback (TangentBasePoint.tangentBasePoint ℂ R d)).obj X))

local instance familyNativeTangent_comm (d : Derivation ℂ R ℂ) : IsCommMonObj (TangentBasePoint.tangentFamily ℂ R X d) :=
  inferInstanceAs (IsCommMonObj ((Over.pullback (TangentBasePoint.tangentBasePoint ℂ R d)).obj X))

local instance familyNativeVanishingH1_complexModule :
    Module ℂ (SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule (TangentBasePoint.fixedFamilyFiber ℂ R X).left) 1) :=
  StructureComplexScalars.structureH1ComplexModule (TangentBasePoint.fixedFamilyFiber ℂ R X)

theorem familyBaseTangentObstruction_zero_native (U : X.left.AffineOpenCover)
    (d : Derivation ℂ R ℂ) (h : Family.BaseTangentObstruction.familyBaseTangentObstruction R X U d = 0)
    (V : (TangentBasePoint.tangentFamily ℂ R X d).left.AffineOpenCover) :
    Dual.ConormalObstructionLinear.dualConormalObstructionLinear (TangentBasePoint.tangentFamily ℂ R X d) V = 0 :=
  (Dual.ConormalObstructionLinear.dualConormalObstructionLinear_zero_iff_product (TangentBasePoint.tangentFamily ℂ R X d) V).mpr
    (ObstructionProduct.familyBaseTangentObstruction_zero_product R X U d h)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyTangent.IntrinsicVanishing
