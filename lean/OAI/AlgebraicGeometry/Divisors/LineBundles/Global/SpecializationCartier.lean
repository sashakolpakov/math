import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.SpecializationPush
import OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.SupportClosure
import OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.CartierFiber

/-! # Specialization Cartier -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Global.SpecializationCartier.BundleCycles

noncomputable section

/-! # LineBundleCycles: global cycle specialization is actual Cartier intersection after closure -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X] (I : X.IdealSheafData)

theorem globalPrimeSpecializationQ_push (W : IrreducibleCloseds X) :
    Finsupp.mapDomain (SpecialFiber.BundleCycles.globalSpecialFiberMap I) (CycleSpecialization.BundleCycles.globalPrimeSpecializationQ I (irreducibleSetEquivPoints W)) =
      Principal.CartierCycle.BundleCycles.principalCartierPointCycle (Specialization.BundleCycles.globalDeformationParameterSection I)
        (irreducibleSetEquivPoints.symm
          (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I (Punctured.DeformationFlat.BundleCycles.puncturedFiberGenericPoint I (irreducibleSetEquivPoints W)))) := by
  let P := CycleClass.Geometric.GenericPoint.reducedSupportIdeal W
  have h := Finsupp.mapDomain_mapRange (SpecialFiber.BundleCycles.globalSpecialFiberMap I)
    (Support.Specialization.BundleCycles.globalClosedSupportSpecialization I P) (fun n : ℤ => (n : ℚ)) Int.cast_zero Int.cast_add
  have hp := congrArg (fun z => Finsupp.mapRange (fun n : ℤ => (n : ℚ)) Int.cast_zero z)
    (SpecializationPush.BundleCycles.globalClosedSupportSpecialization_push I P)
  have hq := Finsupp.mapDomain_mapRange (SupportDeformation.BundleCycles.globalSupportDeformationMap I P)
    (Support.Specialization.BundleCycles.globalSupportParameterDivisor I P) (fun n : ℤ => (n : ℚ)) Int.cast_zero Int.cast_add
  have he := Closed.ImageRegularFunction.BundleCycles.integralClosedImage_regularDivisor (SupportDeformation.BundleCycles.globalSupportDeformationMap I P)
    (Specialization.BundleCycles.globalDeformationParameterSection I)
  have hW := congrArg (Principal.CartierCycle.BundleCycles.principalCartierPointCycle (Specialization.BundleCycles.globalDeformationParameterSection I))
    (Deformation.SupportClosure.BundleCycles.supportDeformationImage_eq_pointClosure I W)
  have hg : CycleSpecialization.BundleCycles.globalPrimeSpecialization I (irreducibleSetEquivPoints W) = Support.Specialization.BundleCycles.globalClosedSupportSpecialization I P :=
    CycleSpecialization.BundleCycles.globalPrimeSpecialization_genericPoint I W
  exact (congrArg (fun z => Finsupp.mapDomain (SpecialFiber.BundleCycles.globalSpecialFiberMap I)
    (Finsupp.mapRange (fun n : ℤ => (n : ℚ)) Int.cast_zero z)) hg).trans
      (h.trans (hp.trans (hq.symm.trans (he.trans hW))))

def deformationClosureCycleExtension : (X →₀ ℚ) →ₗ[ℚ] (Deformation.BundleCycles.globalDeformation I →₀ ℚ) :=
  (Finsupp.lmapDomain ℚ ℚ (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I)).comp (Punctured.DivisorPullback.BundleCycles.puncturedCycleExtension I)

theorem globalCycleSpecialization_push_cartier (z : X →₀ ℚ) :
    Finsupp.mapDomain (SpecialFiber.BundleCycles.globalSpecialFiberMap I) (CycleSpecialization.BundleCycles.globalCycleSpecialization I z) =
      Principal.CartierFiber.BundleCycles.principalCartierPointMap (Specialization.BundleCycles.globalDeformationParameterSection I) (deformationClosureCycleExtension I z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => simp only [map_add, Finsupp.mapDomain_add, hz, hw]
  | single x q =>
    have hc : deformationClosureCycleExtension I (Finsupp.single x q) =
        Finsupp.single (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I (Punctured.DeformationFlat.BundleCycles.puncturedFiberGenericPoint I x)) q := by
      change Finsupp.mapDomain _ (Finsupp.mapDomain _ (Finsupp.single x q)) = _
      rw [Finsupp.mapDomain_single, Finsupp.mapDomain_single]
    rw [CycleSpecialization.BundleCycles.globalCycleSpecialization_single, Finsupp.mapDomain_smul, hc, Principal.CartierFiber.BundleCycles.principalCartierPointMap_single]
    apply congrArg (fun z => q • z)
    have h := globalPrimeSpecializationQ_push I (irreducibleSetEquivPoints.symm x)
    rw [irreducibleSetEquivPoints.apply_symm_apply] at h
    exact h

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Global.SpecializationCartier.BundleCycles
