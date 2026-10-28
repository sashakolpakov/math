import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.ClosedImage
import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.CycleChow

/-! # Principal Chow -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.PrincipalChow.BundleCycles

noncomputable section

/-! # LineBundleCycles: the genuine whole-scheme principal divisor vanishes in its dimension Chow group -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem integralPrincipalPointClass_zero (X : Scheme.{0}) [IsIntegral X]
    [AlgebraicGeometry.IsNoetherian X] (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (d : ℕ) (hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f = d + 1) (g : X.functionField) :
    Point.CycleChow.BundleCycles.pointCycleToChowQ f d (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g) = 0 := by
  have hdiv := ClosedImage.BundleCycles.integralClosedImage_principalDivisor (𝟙 X) g
  change Finsupp.mapDomain id (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g) = _ at hdiv
  rw [Finsupp.mapDomain_id] at hdiv
  rw [hdiv]
  apply Point.CycleChow.BundleCycles.pointCycleToChowQ_principal
  have hdim := CycleClass.Geometric.StratumClosure.schemeTranscendenceDimension_eq_imageClosure (𝟙 X) f
  rw [Category.id_comp] at hdim
  exact hdim.symm.trans hd

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.PrincipalChow.BundleCycles
