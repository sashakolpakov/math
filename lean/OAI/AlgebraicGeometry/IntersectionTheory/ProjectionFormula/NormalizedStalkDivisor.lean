import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SemilocalNormalization
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.DivisorNorm
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Normalization
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.ResidueDegree

/-! # Normalized Stalk Divisor -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NormalizedStalkDivisor

noncomputable section

/-! At each codimension-one point of an integral finite-type scheme, the
actual divisor coefficient is obtained by pushing the principal divisor
from the finite normalization of the stalk. No smoothness or normality of
the original support is assumed. -/

set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry IsDedekindDomain _root_.Order
open scoped Classical BigOperators

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.Order OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.DivisorNorm OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Normalization

universe u

variable {k : Type u} [Field k] [CharZero k]
  {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]

/-- The given rational function in the function field of the actual
normalized stalk spectrum, through the canonical fraction-field maps. -/
def normalizedStalkFunction (x : X) (hx : coheight x = 1) (g : X.functionField) :
    (Spec (.of (integralClosure (X.presheaf.stalk x) X.functionField))).functionField := by
  let S := integralClosure (X.presheaf.stalk x) X.functionField
  let : IsDedekindDomain S := Support.Normalization.stalk_normalization_isDedekind f x hx
  let : IsFractionRing S X.functionField :=
    integralClosure.isFractionRing_of_finite_extension X.functionField X.functionField
  exact Affine.Order.affineFunctionFieldIso S ((FractionRing.algEquiv S X.functionField).symm g)

/-- The weighted principal cycle of the normalized local curve has exactly
the original scheme's order as its coefficient at the closed point. -/
theorem normalizedStalk_pushforward [IsLocallyNoetherian X]
    (x : X) (hx : coheight x = 1) (g : X.functionField) (hg : g ≠ 0) :
    letI := Support.Normalization.stalk_normalization_isDedekind f x hx
    CyclePushforward.pointPushforward (Spec.map (CommRingCat.ofHom
      (algebraMap (X.presheaf.stalk x) (integralClosure (X.presheaf.stalk x) X.functionField))))
      (Affine.DivisorNorm.rationalPrincipalDivisor
        (Spec (.of (integralClosure (X.presheaf.stalk x) X.functionField)))
        (normalizedStalkFunction f x hx g)) =
      Finsupp.single (IsLocalRing.closedPoint (X.presheaf.stalk x) : Spec (X.presheaf.stalk x))
        (X.ord g x : ℚ) := by
  let R := X.presheaf.stalk x
  let S := integralClosure R X.functionField
  let : IsDedekindDomain S := Support.Normalization.stalk_normalization_isDedekind f x hx
  let : Module.Finite R S := Support.Normalization.finite_stalk_normalization f x
  let : IsFractionRing S X.functionField :=
    integralClosure.isFractionRing_of_finite_extension X.functionField X.functionField
  let : Ring.KrullDimLE 1 R := krullDimLE_of_coheight_le hx.le
  let : Finite (HeightOneSpectrum S) := BranchOrder.finite_heightOneSpectrum R S
  let := Fintype.ofFinite (HeightOneSpectrum S)
  rw [Affine.DivisorNorm.pushforward_rationalPrincipalDivisor_local]
  congr 1
  simp_rw [normalizedStalkFunction, Affine.Order.schemeOrder_eq_localOrder]
  rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hx]
  change (∑ P : HeightOneSpectrum S, (P.asIdeal.inertiaDeg R : ℚ) *
    (SemilocalDivisorNorm.localOrder P ((FractionRing.algEquiv S X.functionField).symm g) : ℚ)) =
      ((WithZero.log (Ring.ordFrac R g) : ℤ) : ℚ)
  rw [SemilocalNormalization.log_ordFrac_eq_sum R S X.functionField g hg]
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast]

set_option backward.isDefEq.respectTransparency false in
/-- Composing with the actual stalk-spectrum map gives the original
divisor's coefficient as a cycle on the original scheme. -/
theorem normalizedStalk_pushforward_to_scheme [IsLocallyNoetherian X]
    (x : X) (hx : coheight x = 1) (g : X.functionField) (hg : g ≠ 0) :
    letI := Support.Normalization.stalk_normalization_isDedekind f x hx
    CyclePushforward.pointPushforward (Spec.map (CommRingCat.ofHom
      (algebraMap (X.presheaf.stalk x) (integralClosure (X.presheaf.stalk x) X.functionField))) ≫
        X.fromSpecStalk x)
      (Affine.DivisorNorm.rationalPrincipalDivisor
        (Spec (.of (integralClosure (X.presheaf.stalk x) X.functionField)))
        (normalizedStalkFunction f x hx g)) = Finsupp.single x (X.ord g x : ℚ) := by
  let := Support.Normalization.stalk_normalization_isDedekind f x hx
  rw [CyclePushforward.pointPushforward_comp, LinearMap.comp_apply, normalizedStalk_pushforward f x hx g hg,
    CyclePushforward.pointPushforward_single, Stalk.ResidueDegree.fromSpecStalk_residueDegree,
    Nat.cast_one, mul_one]
  exact congrArg (fun y : X => Finsupp.single y (X.ord g x : ℚ))
    (Scheme.fromSpecStalk_closedPoint (X := X) (x := x))

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NormalizedStalkDivisor
