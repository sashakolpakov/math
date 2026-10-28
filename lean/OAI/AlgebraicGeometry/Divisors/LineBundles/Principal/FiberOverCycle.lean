import OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.CartierFiber
import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.GradedOverPushforward
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SupportSection

/-! # Fiber Over Cycle -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.FiberOverCycle.BundleCycles

noncomputable section

/-! The existing principal Cartier fiber cycle is transported to the literal source structure-map grading. Its full pushforward and every surviving coefficient are retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions

theorem dimensionCycleTransport_apply {X : Scheme} {f g : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} (h : f = g) (d : ℕ)
    (c : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) (x : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint g d)
    (y : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d) (he : x.val = y.val) : DimensionChow.BundleCycles.dimensionCycleTransport h d c x = c y := by
  subst g
  have hxy : x = y := Subtype.ext he
  subst y
  rfl

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [AlgebraicGeometry.IsNoetherian X.left]
  [AlgebraicGeometry.IsNoetherian Y.left] (i : X ⟶ Y) [IsClosedImmersion i.left]

omit [AlgebraicGeometry.IsNoetherian Y.left] in
theorem finiteOverPushforward_closedTransport (d : ℕ) (c : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (i.left ≫ Y.hom) d →₀ ℚ) :
    Finite.GradedOverPushforward.BundleCycles.finiteOverGradedPushforward i d (DimensionChow.BundleCycles.dimensionCycleTransport i.w d c) = Closed.CyclePushforward.BundleCycles.closedDimensionCyclePushforward i.left Y.hom d c := by
  apply Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion_injective Y.hom d
  rw [Finite.GradedOverPushforward.BundleCycles.finiteOverGradedPushforward_forget, DimensionChow.BundleCycles.dimensionCycleTransport_forget, Closed.CyclePushforward.BundleCycles.closedDimensionCyclePushforward_forget]
  exact IsomorphismDivisorPushforward.BundleCycles.pointPushforward_eq_mapDomain_of_immersion i.left _

variable (s : Γ(Y.left, ⊤)) (d : ℕ) (x : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint Y.hom (d + 1))

def principalFiberOverCycle : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d →₀ ℚ :=
  DimensionChow.BundleCycles.dimensionCycleTransport i.w d (CartierFiber.BundleCycles.principalCartierFiberCycle i.left s Y.hom d x)

theorem principalFiberOverCycle_apply (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d) :
    principalFiberOverCycle i s d x z = CartierFiber.BundleCycles.principalCartierGradedCycle s Y.hom d x (Finite.GradedOverPushforward.BundleCycles.finiteOverDimensionPoint i d z) := by
  let w : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (i.left ≫ Y.hom) d :=
    ⟨z.val, (congrArg (fun f => Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm z.val) f) i.w).trans z.property⟩
  have h := dimensionCycleTransport_apply i.w d (CartierFiber.BundleCycles.principalCartierFiberCycle i.left s Y.hom d x) z w rfl
  exact h

variable [LocallyOfFiniteType Y.hom]

theorem principalFiberOverCycle_push (hzero : Set.range i.left = (Y.left.basicOpen s : Set Y.left)ᶜ) :
    Finite.GradedOverPushforward.BundleCycles.finiteOverGradedPushforward i d (principalFiberOverCycle i s d x) = CartierFiber.BundleCycles.principalCartierGradedCycle s Y.hom d x :=
  (finiteOverPushforward_closedTransport i d (CartierFiber.BundleCycles.principalCartierFiberCycle i.left s Y.hom d x)).trans
    (CartierFiber.BundleCycles.principalCartierFiberCycle_push i.left s Y.hom hzero d x)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.FiberOverCycle.BundleCycles
