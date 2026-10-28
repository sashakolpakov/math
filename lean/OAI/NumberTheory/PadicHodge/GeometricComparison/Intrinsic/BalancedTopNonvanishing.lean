import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralPositiveTopProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.PositiveProductNonvanishing
import OAI.NumberTheory.PadicHodge.GeometricComparison.SpecialFiberProjectivity

/-! # Balanced Top Nonvanishing -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The genuine complex top cup supplies a nonzero integral ordinary
product, whose finite reductions force the original balanced rational
crystalline top cup to be nonzero. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

local instance Geometry.AbelianH1Model.balanced_top_integral_separated : A.integral.scheme.left.IsSeparated := ⟨by
  rw [← terminal.comp_from A.integral.scheme.hom]
  infer_instance⟩

def Geometry.AbelianH1Model.balancedTopSpecialProjection : A.specialFiber.scheme.left ⟶ A.integral.scheme.left :=
  pullback.fst A.integral.scheme.hom (Geometry.scalarBaseMap (PadicInt.toZMod : ℤ_[q] →+* ZMod q))

theorem Geometry.AbelianH1Model.balancedTopSpecialSquare :
    IsPullback A.balancedTopSpecialProjection A.specialFiber.scheme.hom A.integral.scheme.hom
      (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[q] →+* ZMod q))) :=
  IsPullback.of_hasPullback _ _

theorem Geometry.AbelianH1Model.nativeBalancedTopCup_nonzero (j : K →+* ℂ)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber j).scheme.left (A.complexFiber j).scheme.hom)
    (hpos : 0 < A.dimension) :
    IntegralComparison.GradedExteriorCup.exteriorPowerCup
      (IntegralComparison.Balanced.RationalCupUnit.data q (ZMod q) A.specialFiber.scheme
        A.specialFiber_projective) (2*A.dimension) ≠ 0 := by
  let d := 2*A.dimension-1
  have hd : d+1 = 2*A.dimension := by dsimp only [d]; omega
  obtain ⟨v, hv⟩ := A.integralPositiveTopProduct_tensor j P d hd
  have h := IntegralComparison.IntrinsicPadic.PositiveProductNonvanishing.Intrinsic.exteriorPowerCup_ne_zero
    q A.integral.scheme A.specialFiber.scheme A.balancedTopSpecialProjection
    A.balancedTopSpecialSquare A.specialFiber_projective d v hv
  exact hd ▸ h

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
