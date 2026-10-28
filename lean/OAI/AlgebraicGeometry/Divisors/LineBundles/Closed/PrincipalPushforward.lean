import OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.SupportImage
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.GlobalSpecialization
import OAI.AlgebraicGeometry.Divisors.LineBundles.RationalDivisorRestriction

/-! # Principal Pushforward -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.PrincipalPushforward.BundleCycles

noncomputable section

/-!
# LineBundleCycles: closed pushforward of the complete principal divisor

The actual isomorphism between a reduced support and its closed image
identifies their function fields and every local-ring order, including
poles. Pushing the finite divisor therefore gives the genuine principal
divisor of the transported rational function on the image support.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory

/-- Principal divisors transport under the actual function-field isomorphism. -/
theorem rationalPrincipalDivisor_iso {A B : Scheme} [IsIntegral A] [IsIntegral B]
    [AlgebraicGeometry.IsNoetherian A] [AlgebraicGeometry.IsNoetherian B]
    (e : A ≅ B) (g : A.functionField) :
    Finsupp.mapDomain e.hom (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor A g) =
      RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor B ((RationalDivisorRestriction.BundleCycles.openFunctionFieldIso e.hom).inv g) := by
  ext y
  obtain ⟨x, rfl⟩ := e.hom.homeomorph.surjective y
  have hi : Function.Injective e.hom := e.hom.homeomorph.injective
  change Finsupp.mapDomain e.hom (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor A g) (e.hom x) =
    RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor B ((RationalDivisorRestriction.BundleCycles.openFunctionFieldIso e.hom).inv g) (e.hom x)
  rw [Finsupp.mapDomain_apply_of_injective hi, RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor_apply,
    RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor_apply]
  have he : RationalDivisorRestriction.BundleCycles.openFunctionFieldMap e.hom ((RationalDivisorRestriction.BundleCycles.openFunctionFieldIso e.hom).inv g) = g :=
    Iso.inv_hom_id_apply (RationalDivisorRestriction.BundleCycles.openFunctionFieldIso e.hom) g
  exact congrArg (fun n : ℤ => (n : ℚ))
    ((congrArg (fun a => A.ord a x) he.symm).trans
      (RationalDivisorRestriction.BundleCycles.ord_openImmersion e.hom ((RationalDivisorRestriction.BundleCycles.openFunctionFieldIso e.hom).inv g) x))

variable {X Y : Scheme} (i : X ⟶ Y) [IsClosedImmersion i]

/-- The same rational function on the actual isomorphic closed-image support. -/
def closedImageRationalFunction (W : TopologicalSpace.IrreducibleCloseds X)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) :
    (CycleClass.Geometric.GenericPoint.reducedSupportScheme (SupportImage.BundleCycles.closedImageSupport i W)).functionField :=
  (RationalDivisorRestriction.BundleCycles.openFunctionFieldIso (SupportImage.BundleCycles.closedSupportImageIso i W).hom).inv g

theorem closedImageRationalFunction_ne_zero (W : TopologicalSpace.IrreducibleCloseds X)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0) :
    closedImageRationalFunction i W g ≠ 0 :=
  (map_ne_zero_iff _ (RationalDivisorRestriction.BundleCycles.openFunctionFieldIso (SupportImage.BundleCycles.closedSupportImageIso i W).hom).inv.hom.injective).mpr hg

variable [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]

/-- Closed pushforward preserves all coefficients of the actual principal divisor. -/
theorem closedPushforward_principalPointDivisor (W : TopologicalSpace.IrreducibleCloseds X)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) :
    Finsupp.mapDomain i (Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g) =
      Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (SupportImage.BundleCycles.closedImageSupport i W) (closedImageRationalFunction i W g) := by
  let e := SupportImage.BundleCycles.closedSupportImageIso i W
  change Finsupp.mapDomain i (Finsupp.embDomain
      ⟨CycleClass.Geometric.GenericPoint.reducedSupportι W, (CycleClass.Geometric.GenericPoint.reducedSupportι W).isClosedEmbedding.injective⟩
      (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) g)) =
    Finsupp.embDomain
      ⟨CycleClass.Geometric.GenericPoint.reducedSupportι (SupportImage.BundleCycles.closedImageSupport i W),
        (CycleClass.Geometric.GenericPoint.reducedSupportι (SupportImage.BundleCycles.closedImageSupport i W)).isClosedEmbedding.injective⟩
      (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (CycleClass.Geometric.GenericPoint.reducedSupportScheme (SupportImage.BundleCycles.closedImageSupport i W))
        ((RationalDivisorRestriction.BundleCycles.openFunctionFieldIso e.hom).inv g))
  rw [Finsupp.embDomain_eq_mapDomain, Finsupp.embDomain_eq_mapDomain, ← Finsupp.mapDomain_comp]
  have hc : i ∘ CycleClass.Geometric.GenericPoint.reducedSupportι W = CycleClass.Geometric.GenericPoint.reducedSupportι (SupportImage.BundleCycles.closedImageSupport i W) ∘ e.hom :=
    funext fun x => (congrArg (fun a => a x) (SupportImage.BundleCycles.closedSupportImageIso_inclusion i W)).symm
  change Finsupp.mapDomain (i ∘ CycleClass.Geometric.GenericPoint.reducedSupportι W) _ = _
  rw [hc, Finsupp.mapDomain_comp, rationalPrincipalDivisor_iso]
  rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.PrincipalPushforward.BundleCycles
