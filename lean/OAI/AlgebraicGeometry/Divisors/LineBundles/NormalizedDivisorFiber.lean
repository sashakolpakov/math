import OAI.AlgebraicGeometry.Divisors.LineBundles.NormalizedLocalField
import OAI.AlgebraicGeometry.Divisors.LineBundles.NormalizationFiber

/-! # Normalized Divisor Fiber -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.NormalizedDivisorFiber.BundleCycles

noncomputable section

/-!
# LineBundleCycles: the complete normalized-local divisor as a cycle on the original scheme

Restriction from the global normalization carries the same principal
divisor, and composition with the stalk-spectrum map places the recovered
coefficient at the original point with residue degree one.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.Order

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Scheme OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Fields OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

variable (X : Scheme) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
variable (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

theorem normalizedLocal_principalDivisor_toScheme (x : X) (hx : coheight x = 1)
    (g : X.functionField) (hg : g ≠ 0) :
    letI := IntersectionTheory.ProjectionFormula.Support.Normalization.stalk_normalization_isDedekind f x hx
    IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward (Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x)
        (integralClosure (X.presheaf.stalk x) X.functionField))) ≫ X.fromSpecStalk x)
      (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor
        (Spec (.of (integralClosure (X.presheaf.stalk x) X.functionField)))
        (Normal.BranchPushforward.BundleCycles.normalizedStalkFieldIso X f x hx g)) = Finsupp.single x (X.ord g x : ℚ) := by
  let := IntersectionTheory.ProjectionFormula.Support.Normalization.stalk_normalization_isDedekind f x hx
  rw [IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward_comp, LinearMap.comp_apply,
    Normal.BranchPushforward.BundleCycles.normalizedLocal_principalDivisor_pushforward X f x hx g hg]
  exact (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward_single (X.fromSpecStalk x)
    (IsLocalRing.closedPoint (X.presheaf.stalk x) : Spec (X.presheaf.stalk x))
    (X.ord g x : ℚ)).trans (by
      rw [IntersectionTheory.ProjectionFormula.Stalk.ResidueDegree.fromSpecStalk_residueDegree, Nat.cast_one, mul_one]
      exact congrArg (fun y : X => Finsupp.single y (X.ord g x : ℚ))
        (Scheme.fromSpecStalk_closedPoint (X := X) (x := x)))

theorem normalizedPrincipalPointDivisor_comap
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] (x : U)
    (hx : coheight (x : X) = 1) (g : X.functionField) :
    letI := NormalizationResidue.BundleCycles.finiteNormalization_noetherian X f
    letI := IntersectionTheory.ProjectionFormula.Support.Normalization.stalk_normalization_isDedekind f x hx
    Finsupp.comapDomain (NormalizationStalkMap.BundleCycles.normalizationStalkMap X U hU x)
      (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X) ((IntersectionTheory.ProjectionFormula.Normalization.Fields.normalizationFieldIso X).hom g))
      (NormalizationStalkMap.BundleCycles.normalizationStalkMap_injective X U hU x).injOn =
        RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor
          (Spec (.of (integralClosure (X.presheaf.stalk x) X.functionField)))
          (Normal.BranchPushforward.BundleCycles.normalizedStalkFieldIso X f x hx g) := by
  let := NormalizationResidue.BundleCycles.finiteNormalization_noetherian X f
  let := IntersectionTheory.ProjectionFormula.Support.Normalization.stalk_normalization_isDedekind f x hx
  ext y
  have h := NormalizationLocalDivisor.BundleCycles.normalizationLocal_ord X U hU x f ((IntersectionTheory.ProjectionFormula.Normalization.Fields.normalizationFieldIso X).hom g) y
  rw [NormalizedLocalField.BundleCycles.normalizationFunction_localRestriction X U hU x f hx g] at h
  exact congrArg (fun n : ℤ => (n : ℚ)) h.symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.NormalizedDivisorFiber.BundleCycles
