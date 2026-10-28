import OAI.AlgebraicGeometry.Divisors.LineBundles.StalkPrimeSupportOrder
import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.SupportDivisorRestriction
import OAI.AlgebraicGeometry.Divisors.LineBundles.Geometric.ResidueNaturality
import OAI.AlgebraicGeometry.Divisors.LineBundles.StalkNormalReciprocity

/-! # Stalk Support Divisor -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.StalkSupportDivisor.BundleCycles

noncomputable section

/-!
# LineBundleCycles: complete prime-support divisors and residues on the actual stalk spectrum
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order

variable (X : Scheme) [AlgebraicGeometry.IsNoetherian X] (x : X) (p : Spec (X.presheaf.stalk x))

theorem pointSupportPrincipalDivisor_fromSpecStalk
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme (StalkPrimeSupport.BundleCycles.stalkPrimeGlobalSupport X x p)).functionField) :
    Finsupp.comapDomain (X.fromSpecStalk x)
      (Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (StalkPrimeSupport.BundleCycles.stalkPrimeGlobalSupport X x p) g)
      (X.fromSpecStalk x).isEmbedding.injective.injOn =
      Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (irreducibleSetEquivPoints.symm p)
        (Point.SupportMap.BundleCycles.pointSupportFunctionFieldMap (X.fromSpecStalk x) p g) := by
  let : IsIso (Point.SupportMap.BundleCycles.pointSupportFunctionFieldMap (X.fromSpecStalk x) p) :=
    StalkPrimeSupportOrder.BundleCycles.pointSupportFunctionFieldMap_fromSpecStalk_isIso X x p
  exact Point.SupportDivisorRestriction.BundleCycles.pointSupportPrincipalDivisor_comap (X.fromSpecStalk x) p
    (X.fromSpecStalk x).isEmbedding.injective (StalkPrimeSupportOrder.BundleCycles.pointSupport_fromSpecStalk_preimage X x p)
    (StalkPrimeSupportOrder.BundleCycles.pointSupportMap_fromSpecStalk_stalkMap_isIso X x p)
    (StalkPrimeSupportOrder.BundleCycles.pointSupportMap_fromSpecStalk_coheight X x p) g

variable [IsIntegral X] (hNormal : ∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y))

theorem normalResidueContribution_fromSpecStalk (hp : coheight p = 1) (g h : X.functionFieldˣ) :
    Finsupp.comapDomain (X.fromSpecStalk x)
      (ResidueCycleFamily.BundleCycles.normalResidueContribution X hNormal g h
        ⟨X.fromSpecStalk x p, (StalkLocalization.BundleCycles.fromSpecStalk_coheight X x p).trans hp⟩)
      (X.fromSpecStalk x).isEmbedding.injective.injOn =
      letI := hNormal x
      ResidueCycleFamily.BundleCycles.normalResidueContribution (Spec (X.presheaf.stalk x))
        (Affine.ProperReciprocity.BundleCycles.affineNormal_stalk_integrallyClosed (X.presheaf.stalk x))
        (Units.map (StalkRationalOrder.BundleCycles.stalkFunctionFieldMap X x).hom.toMonoidHom g)
        (Units.map (StalkRationalOrder.BundleCycles.stalkFunctionFieldMap X x).hom.toMonoidHom h) ⟨p, hp⟩ := by
  let hD : IsDomain (X.presheaf.stalk x) := inferInstance
  let := hNormal x
  let := hNormal (X.fromSpecStalk x p)
  let hP : IsIntegrallyClosed ((Spec (X.presheaf.stalk x)).presheaf.stalk p) :=
    @Affine.ProperReciprocity.BundleCycles.affineNormal_stalk_integrallyClosed (X.presheaf.stalk x) inferInstance hD (hNormal x) p
  let : IsIso ((X.fromSpecStalk x).stalkMap p) := StalkLocalization.BundleCycles.fromSpecStalk_stalkMap_isIso X x p
  let : IsIso (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (X.fromSpecStalk x) (StalkLocalization.BundleCycles.fromSpecStalk_genericPoint X x)) :=
    StalkRationalOrder.BundleCycles.stalkFunctionFieldMap_isIso X x
  unfold ResidueCycleFamily.BundleCycles.normalResidueContribution
  rw [pointSupportPrincipalDivisor_fromSpecStalk X x p]
  exact congrArg (Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (irreducibleSetEquivPoints.symm p))
    (Geometric.ResidueNaturality.BundleCycles.normalPointResidueFunction_morphism (X.fromSpecStalk x) (StalkLocalization.BundleCycles.fromSpecStalk_genericPoint X x) p hp
      ((StalkLocalization.BundleCycles.fromSpecStalk_coheight X x p).trans hp) g h)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.StalkSupportDivisor.BundleCycles
