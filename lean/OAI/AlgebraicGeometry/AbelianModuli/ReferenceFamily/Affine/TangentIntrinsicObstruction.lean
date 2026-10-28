import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.TangentClassifyingMaps
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.FineDualObstruction

/-! # Tangent Intrinsic Obstruction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! On a monic affine chart of a fine PEL model's native complex
fiber, the intrinsic obstruction of the actual classified tangent family
vanishes exactly for the zero original base derivation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [Field K]
    {s N : ℕ} [NeZero N] {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : Models.FinePELModel P iota N) (hM : M.IsFine) (κ : K →+* ℂ)
    (R : Type) [CommRing R] [Algebra ℂ R] [Algebra R ℂ] [IsScalarTower ℂ R ℂ]
    (f : EtaleSplittingAt.EtaleSplitting.affineOver ℂ R ⟶ M.complexFiber κ) [Mono f]

attribute [local instance] Abelian.DualObstructionCriterion.abelianDualFiber_smooth Abelian.DualObstructionCriterion.abelianDualFiber_proper
  Abelian.DualObstructionCriterion.abelianDualFiber_connected Abelian.DualObstructionCriterion.abelianDualFiber_integral Abelian.DualObstructionCriterion.abelianDualH1_complexModule

include hM in
theorem Models.FinePELModel.affineTangentIntrinsicObstruction_zero_iff (d : Derivation ℂ R ℂ)
    (V : (M.universal.pullback (M.affineTangentClassifyingMap κ R f d)).polarized.abelian.scheme.left.AffineOpenCover) :
    Dual.ConormalObstructionLinear.dualConormalObstructionLinear
      (M.universal.pullback (M.affineTangentClassifyingMap κ R f d)).polarized.abelian.scheme V = 0 ↔ d = 0 :=
  (M.dualObstruction_zero_iff_constant hM κ (M.affineTangentClassifyingMap κ R f d) V).trans
    (M.affineTangentClassifyingMap_constant_iff κ R f d)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
