import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.UniversalTangent
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.TangentIntrinsicObstruction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.FineDualObstruction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyTangent.IntrinsicVanishing

/-! # PEL Affine Tangent Injection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The constructed complex-linear base-tangent obstruction is
injective on every monic affine chart of a fine PEL model's native
complex fiber. Zero gives an actual global product, PEL rigidity makes
the original classifying map constant, and the chart detects zero. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [Field K]
    {s N : ℕ} [NeZero N] {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : Models.FinePELModel P iota N) (hM : M.IsFine) (κ : K →+* ℂ)
    (R : Type) [CommRing R] [Algebra ℂ R] [Algebra R ℂ] [IsScalarTower ℂ R ℂ]
    (f : EtaleSplittingAt.EtaleSplitting.affineOver ℂ R ⟶ M.complexFiber κ) [Mono f]

attribute [local instance] Abelian.Tangent.abelianFamilyFixedFiber_smooth Abelian.Tangent.abelianFamilyFixedFiber_proper
  Abelian.Tangent.abelianFamilyFixedFiber_connected Abelian.Tangent.abelianFamilyFixedFiber_integral FamilyTangent.IntrinsicVanishing.familyNativeFixedFiber_group
  Abelian.DualObstructionCriterion.abelianDualFiber_smooth Abelian.DualObstructionCriterion.abelianDualFiber_proper Abelian.DualObstructionCriterion.abelianDualFiber_connected Abelian.DualObstructionCriterion.abelianDualFiber_integral
  Abelian.DualObstructionCriterion.abelianDualH1_complexModule

local instance Models.FinePELModel.affineTangentInjectionH1_complexModule : Module ℂ
    (SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule (TangentBasePoint.fixedFamilyFiber ℂ R (M.affineUniversalFamily κ R f)).left) 1) :=
  StructureComplexScalars.structureH1ComplexModule (TangentBasePoint.fixedFamilyFiber ℂ R (M.affineUniversalFamily κ R f))

include hM in
theorem Models.FinePELModel.affineFamilyTangentObstruction_zero (U : (M.affineUniversalFamily κ R f).left.AffineOpenCover)
    (d : Derivation ℂ R ℂ)
    (h : Family.BaseTangentObstruction.familyBaseTangentObstruction R (M.affineUniversalFamily κ R f) U d = 0) : d = 0 := by
  obtain ⟨a, ha⟩ := FamilyTangent.Primitives.familyTangentDerivationPrimitive_of_obstruction_zero R (M.affineUniversalFamily κ R f) U d h
  let V := (M.universal.pullback (M.affineTangentClassifyingMap κ R f d)).polarized.abelian.scheme.left.affineOpenCover
  apply (M.affineTangentIntrinsicObstruction_zero_iff hM κ R f d V).mp
  exact PEL.FineDualObstruction.pelDualObstruction_zero_of_schemeProduct κ
    (M.universal.pullback (M.affineTangentClassifyingMap κ R f d))
    (TangentBasePoint.fixedFamilyFiber ℂ R (M.affineUniversalFamily κ R f)) (M.affineClassifiedTangentProduct κ R f U d a ha) V

include hM in
theorem Models.FinePELModel.affineFamilyTangentObstruction_injective (U : (M.affineUniversalFamily κ R f).left.AffineOpenCover) :
    Function.Injective (Family.BaseTangentObstruction.familyBaseTangentObstruction R (M.affineUniversalFamily κ R f) U) := by
  intro d e h
  apply sub_eq_zero.mp
  apply M.affineFamilyTangentObstruction_zero hM κ R f U (d - e)
  rw [map_sub, h, sub_self]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
