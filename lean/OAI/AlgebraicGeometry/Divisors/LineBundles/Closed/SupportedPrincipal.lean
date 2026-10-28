import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.CycleChow
import OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.PrincipalPushforward

/-! # Supported Principal -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.SupportedPrincipal.BundleCycles

noncomputable section

/-!
# LineBundleCycles: an actual principal divisor on a closed-fiber support has zero fiber class

A lift of its generic point gives the corresponding reduced support
inside the closed subscheme. The existing closed-image isomorphism
transports the actual rational function and complete divisor there.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X Z : Scheme} [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Z]
    (j : Z ⟶ X) [IsClosedImmersion j] (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (d : ℕ)

theorem closedPointCycleToChowQ_imagePrincipal (V : IrreducibleCloseds Z)
    (hV : Foundations.Scheme.SupportDimension.supportTranscendenceDimension V (j ≫ f) = d + 1)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme (SupportImage.BundleCycles.closedImageSupport j V)).functionField) :
    Point.CycleChow.BundleCycles.closedPointCycleToChowQ j f d (Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (SupportImage.BundleCycles.closedImageSupport j V) g) = 0 := by
  let e := RationalDivisorRestriction.BundleCycles.openFunctionFieldIso (SupportImage.BundleCycles.closedSupportImageIso j V).hom
  let gV := e.hom g
  have hg : PrincipalPushforward.BundleCycles.closedImageRationalFunction j V gV = g := Iso.hom_inv_id_apply e g
  have hd := PrincipalPushforward.BundleCycles.closedPushforward_principalPointDivisor j V gV
  rw [hg] at hd
  rw [← hd, Point.CycleChow.BundleCycles.closedPointCycleToChowQ_pushforward]
  exact Point.CycleChow.BundleCycles.pointCycleToChowQ_principal (j ≫ f) d V hV gV

theorem closedPointCycleToChowQ_supportedPrincipal (W : IrreducibleCloseds X)
    (hW : Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f = d + 1)
    (hs : (W : Set X) ⊆ Set.range j) (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) :
    Point.CycleChow.BundleCycles.closedPointCycleToChowQ j f d (Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g) = 0 := by
  have hw : irreducibleSetEquivPoints W ∈ (W : Set X) := by
    rw [← CycleClass.Geometric.GenericPoint.range_reducedSupportι W]
    exact ⟨genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W), CycleClass.Geometric.GenericPoint.reducedSupport_genericPoint_eq W⟩
  obtain ⟨z, hz⟩ := hs hw
  let V := irreducibleSetEquivPoints.symm z
  have hV : SupportImage.BundleCycles.closedImageSupport j V = W := by
    rw [SupportImage.BundleCycles.closedImageSupport_eq_pointClosure, irreducibleSetEquivPoints.apply_symm_apply, hz,
      irreducibleSetEquivPoints.symm_apply_apply]
  subst W
  exact closedPointCycleToChowQ_imagePrincipal j f d V
    ((SupportImage.BundleCycles.closedImageSupport_dimension j f V).symm.trans hW) g

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.SupportedPrincipal.BundleCycles
