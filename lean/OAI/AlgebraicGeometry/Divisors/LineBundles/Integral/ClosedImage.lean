import OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.PrincipalPushforward

/-! # Closed Image -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.ClosedImage.BundleCycles

noncomputable section

/-!
# LineBundleCycles: a closed integral scheme and its actual reduced image support

The canonical map from an integral closed subscheme to its reduced image
is an isomorphism. Its transported principal divisor is exactly the
closed pushforward of the original divisor, coefficient by coefficient.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {A X : Scheme} [IsIntegral A] (i : A ⟶ X) [IsClosedImmersion i]

def integralClosedImageIso : A ≅ CycleClass.Geometric.GenericPoint.reducedSupportScheme (CycleClass.Geometric.StratumClosure.integralImageClosure i) := by
  have he : IsIso (CycleClass.Geometric.StratumClosure.toReducedImageClosure i) := by
    change IsIso (i.toImage ≫ (CycleClass.Geometric.StratumClosure.reducedImageClosureIso i).hom)
    infer_instance
  exact @asIso _ _ _ _ (CycleClass.Geometric.StratumClosure.toReducedImageClosure i) he

theorem integralClosedImageIso_inclusion :
    (integralClosedImageIso i).hom ≫ CycleClass.Geometric.GenericPoint.reducedSupportι (CycleClass.Geometric.StratumClosure.integralImageClosure i) = i :=
  CycleClass.Geometric.StratumClosure.toReducedImageClosure_inclusion i

theorem integralClosedImage_genericPoint :
    irreducibleSetEquivPoints (CycleClass.Geometric.StratumClosure.integralImageClosure i) = i (genericPoint A) := by
  have hc := congrArg (fun j : A ⟶ X => j (genericPoint A)) (integralClosedImageIso_inclusion i)
  have hg := genericPoint_eq_of_isOpenImmersion (integralClosedImageIso i).hom
  exact (CycleClass.Geometric.GenericPoint.reducedSupport_genericPoint_eq (CycleClass.Geometric.StratumClosure.integralImageClosure i)).symm.trans
    ((congrArg (CycleClass.Geometric.GenericPoint.reducedSupportι (CycleClass.Geometric.StratumClosure.integralImageClosure i)) hg).symm.trans hc)

def integralClosedImageFunction (g : A.functionField) :
    (CycleClass.Geometric.GenericPoint.reducedSupportScheme (CycleClass.Geometric.StratumClosure.integralImageClosure i)).functionField :=
  (RationalDivisorRestriction.BundleCycles.openFunctionFieldIso (integralClosedImageIso i).hom).inv g

theorem integralClosedImageFunction_ne_zero (g : A.functionField) (hg : g ≠ 0) :
    integralClosedImageFunction i g ≠ 0 :=
  (map_ne_zero_iff _ (RationalDivisorRestriction.BundleCycles.openFunctionFieldIso (integralClosedImageIso i).hom).inv.hom.injective).mpr hg

variable [AlgebraicGeometry.IsNoetherian A] [AlgebraicGeometry.IsNoetherian X]

theorem integralClosedImage_principalDivisor (g : A.functionField) :
    Finsupp.mapDomain i (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor A g) =
      Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (CycleClass.Geometric.StratumClosure.integralImageClosure i) (integralClosedImageFunction i g) := by
  let e := integralClosedImageIso i
  have hc : CycleClass.Geometric.GenericPoint.reducedSupportι (CycleClass.Geometric.StratumClosure.integralImageClosure i) ∘ e.hom = i :=
    funext (fun a => congrArg (fun j : A ⟶ X => j a) (integralClosedImageIso_inclusion i))
  unfold Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor
  change Finsupp.mapDomain i (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor A g) =
    Finsupp.embDomain ⟨CycleClass.Geometric.GenericPoint.reducedSupportι (CycleClass.Geometric.StratumClosure.integralImageClosure i),
      (CycleClass.Geometric.GenericPoint.reducedSupportι (CycleClass.Geometric.StratumClosure.integralImageClosure i)).isClosedEmbedding.injective⟩
      (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (CycleClass.Geometric.GenericPoint.reducedSupportScheme (CycleClass.Geometric.StratumClosure.integralImageClosure i))
        ((RationalDivisorRestriction.BundleCycles.openFunctionFieldIso e.hom).inv g))
  rw [Finsupp.embDomain_eq_mapDomain, ← Closed.PrincipalPushforward.BundleCycles.rationalPrincipalDivisor_iso e g,
    ← Finsupp.mapDomain_comp]
  exact congrArg (fun j : A → X => Finsupp.mapDomain j (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor A g)) hc.symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.ClosedImage.BundleCycles
