import OAI.AlgebraicGeometry.Picard.ThetaConstruction.ZeroChernHomogeneity
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntrinsicChernClassDetection
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralChernVanishing
import OAI.AlgebraicGeometry.Picard.Homomorphisms.SchemeGroup

/-! # Same Chern Homogeneity -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.SameChernHomogeneity.Geometric

noncomputable section

/-! Two actual algebraic lines with equal native Chern pairings differ
by a homogeneous line. The integral obstruction is eliminated using
injectivity of the original coefficient map on this abelian variety. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralChernVanishing

def originalChernAddHom (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) :
    Additive (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass X.carrier) →+
      AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (Betti.Scheme.schemePointSpace X.toOver) 2 where
  toFun q := AbelianModuli.ReferenceFamily.Intrinsic.ChernClasses.lineBundleClassChernClass X q.toMul
  map_zero' := AbelianModuli.ReferenceFamily.HomogeneousChernVanishing.lineBundleClassChernClass_one X
  map_add' q r := AbelianModuli.ReferenceFamily.HomogeneousChernVanishing.lineBundleClassChernClass_mul X q.toMul r.toMul

theorem originalChern_tensor_dual (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (L K : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.carrier) :
    AbelianModuli.ReferenceFamily.Intrinsic.ChernClasses.lineBundleChernClass X (L.tensor (Homomorphisms.LineBundleDual.Construction.lineBundleDual K)) =
      AbelianModuli.ReferenceFamily.Intrinsic.ChernClasses.lineBundleChernClass X L - AbelianModuli.ReferenceFamily.Intrinsic.ChernClasses.lineBundleChernClass X K := by
  have hk : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (Homomorphisms.LineBundleDual.Construction.lineBundleDual K) =
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf K)⁻¹ :=
    eq_inv_of_mul_eq_one_left (Homomorphisms.LineBundleEvaluation.Construction.tensorClass_dual (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf K))
  have hclass : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.tensor (Homomorphisms.LineBundleDual.Construction.lineBundleDual K)) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L / AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf K := by
    exact (Homomorphisms.SchemeGroup.Construction.lineBundleClass_mul L (Homomorphisms.LineBundleDual.Construction.lineBundleDual K)).symm.trans
      ((congrArg (fun q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass X.carrier => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L * q) hk).trans
        (div_eq_mul_inv (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf K)).symm)
  exact (congrArg (AbelianModuli.ReferenceFamily.Intrinsic.ChernClasses.lineBundleClassChernClass X) hclass).trans
    (map_sub (originalChernAddHom X) (Additive.ofMul (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L))
      (Additive.ofMul (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf K)))

section Integral
variable (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)

local instance : AddCommGroup (DivisorClass.Chern.Holomorphic.Connecting.integralSheafCohomologyTwo A.variety.analyticSpace) :=
  AbelianModuli.ReferenceFamily.Cech.Add.cechClassAddCommGroup (X := TopCat.of A.variety.analyticSpace)
    (DivisorClass.Chern.IntegralConstantSheaf.integralConstantSheaf (TopCat.of A.variety.analyticSpace)) 2
local instance : AddCommGroup (DivisorClass.Chern.Rational.HolomorphicPeriod.rationalSheafCohomologyTwo A.variety.analyticSpace) :=
  AbelianModuli.ReferenceFamily.Cech.Add.cechClassAddCommGroup (X := TopCat.of A.variety.analyticSpace)
    (DivisorClass.Chern.Rational.HolomorphicPeriod.rationalConstantAbelianSheaf (TopCat.of A.variety.analyticSpace)) 2

theorem zeroRationalChern_integralConnecting (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.toOver.left)
    (hL : AbelianModuli.ReferenceFamily.Intrinsic.ChernClasses.lineBundleChernClass A.variety.presentation L = 0) :
    DivisorClass.Chern.Holomorphic.Connecting.holomorphicExponentialConnecting A.variety.analyticModel A.variety.analyticSpace
      (AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicLineClass.nativeHolomorphicLineClass A.variety L) = 0 := by
  let := AlgebraicTopology.Cohomology.Singular.ChartLocalContractible.stronglyLocallyContractibleSpace_of_chartedSpace A.variety.analyticModel A.variety.analyticSpace
  let := AlgebraicTopology.Cohomology.Singular.ChartLocalContractible.locallyPathConnectedSpace_of_chartedSpace A.variety.analyticModel A.variety.analyticSpace
  have hc := DivisorClass.Chern.Holomorphic.Additive.holomorphicFirstChernClassQ_connecting A.variety.analyticModel A.variety.analyticSpace
    (AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicLineClass.nativeHolomorphicLineClass A.variety L)
  have hq := congrArg (DivisorClass.Chern.Rational.BettiCechSheafComparison.rationalBettiCechSheafEquiv (TopCat.of A.variety.analyticSpace) 1)
    ((AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicChernComparison.nativeHolomorphicLineClass_chern A.variety L).trans hL)
  have hz := hc.symm.trans (hq.trans
    (map_zero (DivisorClass.Chern.Rational.BettiCechSheafComparison.rationalBettiCechSheafIso (TopCat.of A.variety.analyticSpace) 1).hom.hom))
  apply AbelianModuli.ReferenceFamily.Intrinsic.IntegralChernVanishing.nativeIntegralRationalSheaf_injective A
  exact hz.trans (map_zero (DivisorClass.Chern.Rational.HolomorphicPeriod.integralToRationalSheafCohomology A.variety.analyticSpace)).symm

end Integral

namespace AlgebraicPeriodModel
variable {g : ℕ} {E : DefinitionsIntegral.IntegralMatrix g} {T : DefinitionsIntegral.MarkedPolarizedTorus g E}
    (M : PeriodModel.Geometric.AlgebraicPeriodModel T)

theorem _root_.OAI.AlgebraicGeometry.Picard.ThetaConstruction.PeriodModel.Geometric.AlgebraicPeriodModel.sameChern_ratio_homogeneous (hE : E.transpose = -E)
    (L K : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle M.abelian.toOver.left)
    (h : AbelianModuli.ReferenceFamily.Intrinsic.ChernClasses.lineBundleChernClass M.abelian.variety.presentation L =
      AbelianModuli.ReferenceFamily.Intrinsic.ChernClasses.lineBundleChernClass M.abelian.variety.presentation K) :
    AbelianModuli.ReferenceFamily.HomogeneousLinePowers.IsHomogeneousLineClass M.abelianScheme
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.tensor (Homomorphisms.LineBundleDual.Construction.lineBundleDual K))) := by
  apply M.zeroIntegralChern_homogeneous hE
  apply zeroRationalChern_integralConnecting
  exact (originalChern_tensor_dual M.abelian.variety.presentation L K).trans (sub_eq_zero.mpr h)

theorem _root_.OAI.AlgebraicGeometry.Picard.ThetaConstruction.PeriodModel.Geometric.AlgebraicPeriodModel.sameIntegralPairing_ratio_homogeneous (hE : E.transpose = -E)
    (L K : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle M.abelian.toOver.left)
    (h : ∀ l m : T.lattice,
      AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm M.abelian L (M.nativeIntegralPeriod l) (M.nativeIntegralPeriod m) =
        AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm M.abelian K (M.nativeIntegralPeriod l) (M.nativeIntegralPeriod m)) :
    AbelianModuli.ReferenceFamily.HomogeneousLinePowers.IsHomogeneousLineClass M.abelianScheme
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.tensor (Homomorphisms.LineBundleDual.Construction.lineBundleDual K))) :=
  M.sameChern_ratio_homogeneous hE L K (M.nativeChernClass_eq_of_integral_pairing L K h)

end AlgebraicPeriodModel

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.SameChernHomogeneity.Geometric
