import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.DualObstructionCriterion
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PELDoublePullbackClasses
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Product.IsoReidentifiedFiber

/-! # Fine Dual Obstruction -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.AbelianModuli.ReferenceFamily

/-! For the actual universal family of a fine PEL model, the native
obstruction vanishes exactly when its dual-number classifying map is the
constant extension of its reduction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [Field K]
    {s N : ℕ} [NeZero N] {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : Models.FinePELModel P iota N) (hM : M.IsFine) (κ : K →+* ℂ)
    (f : PEL.ComplexDualTests.pelComplexDualTest κ ⟶ M.space)

attribute [local instance] Abelian.DualObstructionCriterion.abelianDualFiber_smooth Abelian.DualObstructionCriterion.abelianDualFiber_proper
  Abelian.DualObstructionCriterion.abelianDualFiber_connected Abelian.DualObstructionCriterion.abelianDualFiber_integral Abelian.DualObstructionCriterion.abelianDualH1_complexModule

include hM in
theorem Models.FinePELModel.dualObstruction_zero_iff_constant (U : (M.universal.pullback f).polarized.abelian.scheme.left.AffineOpenCover) :
    Dual.ConormalObstructionLinear.dualConormalObstructionLinear (M.universal.pullback f).polarized.abelian.scheme U = 0 ↔
      f = PEL.ComplexDualTests.pelComplexDualProjection κ ≫ PEL.ComplexDualTests.pelComplexDualReduction κ ≫ f :=
  (PEL.DualObstructionCriterion.pelDualObstruction_zero_iff_class κ (M.universal.pullback f) U).trans
    (M.universal_class_eq_doublePullback_iff hM f (PEL.ComplexDualTests.pelComplexDualReduction κ) (PEL.ComplexDualTests.pelComplexDualProjection κ))

end AlgebraicGeometry.AbelianModuli.ReferenceFamily

namespace AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.FineDualObstruction

/-! An actual scheme product of a PEL deformation with any fixed
complex fiber makes its intrinsic native obstruction vanish. The product
is first normalized on the deformation's own actual special fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E] [Field K]
    {s N : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (κ : K →+* ℂ) (A : Objects.PELObject P iota N (ComplexDualTests.pelComplexDualTest κ))

attribute [local instance] Abelian.DualObstructionCriterion.abelianDualFiber_smooth Abelian.DualObstructionCriterion.abelianDualFiber_proper
  Abelian.DualObstructionCriterion.abelianDualFiber_connected Abelian.DualObstructionCriterion.abelianDualFiber_integral Abelian.DualObstructionCriterion.abelianDualH1_complexModule
attribute [local irreducible] Normalized.SmoothAffineDualProduct.dualProductSpecialFiberIso

theorem pelDualObstruction_zero_of_schemeProduct (B : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    (e : A.polarized.abelian.scheme ≅ (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection ℂ)).obj B)
    (V : A.polarized.abelian.scheme.left.AffineOpenCover) :
    Dual.ConormalObstructionLinear.dualConormalObstructionLinear A.polarized.abelian.scheme V = 0 := by
  apply (Dual.ConormalObstructionLinear.dualConormalObstructionLinear_zero_iff_product A.polarized.abelian.scheme V).mpr
  exact ⟨Product.IsoReidentifiedFiber.productIsoCanonicalFiber (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection ℂ))
      (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction ℂ)) (Normalized.SmoothAffineDualProduct.dualProductSpecialFiberIso ℂ) A.polarized.abelian.scheme B e,
    Product.IsoReidentifiedFiber.productIsoCanonicalFiber_normalized (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection ℂ))
      (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction ℂ)) (Normalized.SmoothAffineDualProduct.dualProductSpecialFiberIso ℂ) A.polarized.abelian.scheme B e⟩

end AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.FineDualObstruction

end

end OAI
