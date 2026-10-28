import OAI.AlgebraicGeometry.CycleClass.Thom.NormalizedLocalField
import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Fiber

/-! # Normalized Divisor Fiber -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.NormalizedDivisorFiber.Constructions.NormalizationLocal

noncomputable section

/-!
# ThomClass: the complete normalized-local divisor as a cycle on the original scheme

Restriction from the global normalization carries the same principal
divisor, and composition with the stalk-spectrum map places the recovered
coefficient at the original point with residue degree one.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.Order

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Field.Constructions

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Scheme.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Fields.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Point.Constructions

variable (X : Scheme) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
variable (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

theorem normalizedLocal_principalDivisor_toScheme (x : X) (hx : coheight x = 1)
    (g : X.functionField) (hg : g ≠ 0) :
    letI := SupportNormalization.Constructions.stalk_normalization_isDedekind f x hx
    Point.Constructions.pointPushforward (Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x)
        (integralClosure (X.presheaf.stalk x) X.functionField))) ≫ X.fromSpecStalk x)
      (Point.Constructions.rationalPrincipalPointDivisor
        (Spec (.of (integralClosure (X.presheaf.stalk x) X.functionField)))
        (Normal.BranchPushforward.Constructions.NormalizationLocal.normalizedStalkFieldIso X f x hx g)) = Finsupp.single x (X.ord g x : ℚ) := by
  let := SupportNormalization.Constructions.stalk_normalization_isDedekind f x hx
  rw [Point.Constructions.pointPushforward_comp, LinearMap.comp_apply,
    Normal.BranchPushforward.Constructions.NormalizationLocal.normalizedLocal_principalDivisor_pushforward X f x hx g hg]
  exact (Point.Constructions.pointPushforward_single (X.fromSpecStalk x)
    (IsLocalRing.closedPoint (X.presheaf.stalk x) : Spec (X.presheaf.stalk x))
    (X.ord g x : ℚ)).trans (by
      rw [StalkResidueDegree.Constructions.fromSpecStalk_residueDegree, Nat.cast_one, mul_one]
      exact congrArg (fun y : X => Finsupp.single y (X.ord g x : ℚ))
        (Scheme.fromSpecStalk_closedPoint (X := X) (x := x)))

theorem normalizedPrincipalPointDivisor_comap
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] (x : U)
    (hx : coheight (x : X) = 1) (g : X.functionField) :
    letI := Normalization.Field.Constructions.finiteNormalization_noetherian X f
    letI := SupportNormalization.Constructions.stalk_normalization_isDedekind f x hx
    Finsupp.comapDomain (Normalization.StalkMap.Constructions.Local.normalizationStalkMap X U hU x)
      (Point.Constructions.rationalPrincipalPointDivisor (Normalization.Scheme.Constructions.normalization X) ((Normalization.Fields.Constructions.normalizationFieldIso X).hom g))
      (Normalization.StalkMap.Constructions.Local.normalizationStalkMap_injective X U hU x).injOn =
        Point.Constructions.rationalPrincipalPointDivisor
          (Spec (.of (integralClosure (X.presheaf.stalk x) X.functionField)))
          (Normal.BranchPushforward.Constructions.NormalizationLocal.normalizedStalkFieldIso X f x hx g) := by
  let := Normalization.Field.Constructions.finiteNormalization_noetherian X f
  let := SupportNormalization.Constructions.stalk_normalization_isDedekind f x hx
  ext y
  have h := Normalization.LocalDivisor.Constructions.normalizationLocal_ord X U hU x f ((Normalization.Fields.Constructions.normalizationFieldIso X).hom g) y
  rw [NormalizedLocalField.Constructions.Normalization.normalizationFunction_localRestriction X U hU x f hx g] at h
  exact congrArg (fun n : ℤ => (n : ℚ)) h.symm

end

end OAI.AlgebraicGeometry.CycleClass.Thom.NormalizedDivisorFiber.Constructions.NormalizationLocal
