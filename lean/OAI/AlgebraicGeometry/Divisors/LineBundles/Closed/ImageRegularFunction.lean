import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.ClosedImage
import OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.CartierCycle

/-! # Image Regular Function -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.ImageRegularFunction.BundleCycles

noncomputable section

/-!
# LineBundleCycles: transported functions on closed images are the actual regular restrictions

The canonical generic-field isomorphism commutes with global germs and
the actual closed-immersion pullback. Thus the function used in the
image principal-divisor formula is precisely the restricted equation.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {A X : Scheme} [IsIntegral A] (i : A ⟶ X) [IsClosedImmersion i]
variable [AlgebraicGeometry.IsNoetherian A] [AlgebraicGeometry.IsNoetherian X]

omit [AlgebraicGeometry.IsNoetherian A] [AlgebraicGeometry.IsNoetherian X] in
theorem integralClosedImageFunction_regular (a : Γ(X, ⊤)) :
    Integral.ClosedImage.BundleCycles.integralClosedImageFunction i (RegularDivisor.BundleCycles.globalFunctionFieldElement A (i.appTop a)) =
      Principal.CartierCycle.BundleCycles.supportRegularFunction a (CycleClass.Geometric.StratumClosure.integralImageClosure i) := by
  let e := Integral.ClosedImage.BundleCycles.integralClosedImageIso i
  let j := CycleClass.Geometric.GenericPoint.reducedSupportι (CycleClass.Geometric.StratumClosure.integralImageClosure i)
  have hc : j.appTop ≫ e.hom.appTop = i.appTop :=
    (Scheme.Hom.comp_appTop e.hom j).symm.trans
      (congrArg Scheme.Hom.appTop (Integral.ClosedImage.BundleCycles.integralClosedImageIso_inclusion i))
  have hg := Cycles.Functoriality.FunctionFields.Construction.genericFieldMap_germ e.hom (genericPoint_eq_of_isOpenImmersion e.hom)
  have hv : RationalDivisorRestriction.BundleCycles.openFunctionFieldMap e.hom (Principal.CartierCycle.BundleCycles.supportRegularFunction a (CycleClass.Geometric.StratumClosure.integralImageClosure i)) =
      RegularDivisor.BundleCycles.globalFunctionFieldElement A (e.hom.appTop (j.appTop a)) :=
    congrArg (fun k : Γ(CycleClass.Geometric.GenericPoint.reducedSupportScheme (CycleClass.Geometric.StratumClosure.integralImageClosure i), ⊤) ⟶ A.functionField =>
      k (j.appTop a)) hg
  have hf := hv.trans (congrArg (RegularDivisor.BundleCycles.globalFunctionFieldElement A)
    (congrArg (fun k : Γ(X, ⊤) ⟶ Γ(A, ⊤) => k a) hc))
  apply (RationalDivisorRestriction.BundleCycles.openFunctionFieldIso e.hom).hom.hom.injective
  exact (Iso.inv_hom_id_apply (RationalDivisorRestriction.BundleCycles.openFunctionFieldIso e.hom)
    (RegularDivisor.BundleCycles.globalFunctionFieldElement A (i.appTop a))).trans hf.symm

theorem integralClosedImage_regularDivisor (a : Γ(X, ⊤)) :
    Finsupp.mapDomain i (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor A (RegularDivisor.BundleCycles.globalFunctionFieldElement A (i.appTop a))) =
      Principal.CartierCycle.BundleCycles.principalCartierPointCycle a (CycleClass.Geometric.StratumClosure.integralImageClosure i) := by
  rw [Integral.ClosedImage.BundleCycles.integralClosedImage_principalDivisor, integralClosedImageFunction_regular]
  rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.ImageRegularFunction.BundleCycles
