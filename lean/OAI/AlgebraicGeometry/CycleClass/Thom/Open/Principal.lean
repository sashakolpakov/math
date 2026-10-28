import OAI.AlgebraicGeometry.CycleClass.Thom.RationalOrderTransport
import OAI.AlgebraicGeometry.CycleClass.Thom.PushforwardFiber

/-! # Principal -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.Open.Principal.Constructions

/-! Removing a closed set of intrinsic codimension at least two leaves
the entire principal divisor unchanged under actual open pushforward. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.RationalOrderTransport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Point.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.PushforwardFiber.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ResidueDegree.Constructions

instance openScheme_isNoetherian (X : Scheme) [AlgebraicGeometry.IsNoetherian X]
    (U : X.Opens) : AlgebraicGeometry.IsNoetherian (U : Scheme) := by
  let : CompactSpace (U : Scheme) := QuasiCompact.compactSpace_of_compactSpace U.ι
  exact ⟨⟩

theorem principalDivisor_open_pushforward (X : Scheme) [IsIntegral X]
    [AlgebraicGeometry.IsNoetherian X] (U : X.Opens) [Nonempty U]
    (hU : ∀ x : X, Order.coheight x = 1 → x ∈ U) (g : X.functionField) :
    Point.Constructions.pointPushforward U.ι
      (Point.Constructions.rationalPrincipalPointDivisor U (RationalOrderTransport.Constructions.openFunctionFieldMap U.ι g)) =
        Point.Constructions.rationalPrincipalPointDivisor X g := by
  ext x
  by_cases hx : x ∈ U
  · let y : (U : Scheme) := ⟨x, hx⟩
    rw [PushforwardFiber.Constructions.pointPushforward_uniqueFiber U.ι y x rfl
      (fun z hz => U.ι.isOpenEmbedding.injective hz), ResidueDegree.Constructions.residueDegree_immersion U.ι y,
      Nat.cast_one, mul_one, Point.Constructions.rationalPrincipalPointDivisor_apply,
      Point.Constructions.rationalPrincipalPointDivisor_apply, RationalOrderTransport.Constructions.ord_openImmersion]
    rfl
  · rw [Point.Constructions.rationalPrincipalPointDivisor_apply,
      Scheme.ord_eq_zero_of_coheight_neq_one (fun h => hx (hU x h)), Int.cast_zero]
    apply PushforwardFiber.Constructions.pointPushforward_apply_eq_zero
    intro y _ he
    exact hx (he ▸ y.property)

end AlgebraicGeometry.CycleClass.Thom.Open.Principal.Constructions

namespace AlgebraicGeometry.CycleClass.Thom.Open.Principal.Constructions.FiberCoefficients

/-! An arbitrary actual open immersion preserves principal-divisor
coefficients on every fully retained pushforward fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.CycleClass.Thom.RationalOrderTransport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Point.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.PushforwardFiber.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ResidueDegree.Constructions

variable {X S : Scheme} [IsIntegral X] [IsIntegral S]
  [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian S]
  (a : X ⟶ S) [IsOpenImmersion a] (g : S.functionField)

theorem principalPointDivisor_open_comap :
    Point.Constructions.rationalPrincipalPointDivisor X (RationalOrderTransport.Constructions.openFunctionFieldMap a g) =
      Finsupp.comapDomain a (Point.Constructions.rationalPrincipalPointDivisor S g) a.isOpenEmbedding.injective.injOn := by
  ext x
  rw [Finsupp.comapDomain_apply, Point.Constructions.rationalPrincipalPointDivisor_apply, Point.Constructions.rationalPrincipalPointDivisor_apply,
    RationalOrderTransport.Constructions.ord_openImmersion]

theorem principalPointDivisor_open_fiber_coefficient {T : Scheme} (f : S ⟶ T) (x : T)
    (hcover : ∀ y : S, f y = x → y ∈ Set.range a) :
    Point.Constructions.pointPushforward (a ≫ f) (Point.Constructions.rationalPrincipalPointDivisor X (RationalOrderTransport.Constructions.openFunctionFieldMap a g)) x =
      Point.Constructions.pointPushforward f (Point.Constructions.rationalPrincipalPointDivisor S g) x := by
  have h := PushforwardFiber.Constructions.pointPushforward_coeff_of_fiber_cover a f x a.isOpenEmbedding.injective
    (ResidueDegree.Constructions.residueDegree_immersion a) hcover (Point.Constructions.rationalPrincipalPointDivisor S g)
  rw [← principalPointDivisor_open_comap a g] at h
  exact h.symm

end AlgebraicGeometry.CycleClass.Thom.Open.Principal.Constructions.FiberCoefficients

end

end OAI
