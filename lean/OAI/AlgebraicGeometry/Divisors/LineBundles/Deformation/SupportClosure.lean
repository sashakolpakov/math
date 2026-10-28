import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.ChowSpecialization

/-! # Support Closure -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.SupportClosure.BundleCycles

noncomputable section

/-! # LineBundleCycles: the closure of an extended cycle is its actual support deformation -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X : Scheme.{0}} (I : X.IdealSheafData) (W : IrreducibleCloseds X)

theorem puncturedGenericPoint_deformationInclusion :
    ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I (Punctured.DeformationFlat.BundleCycles.puncturedFiberGenericPoint I (irreducibleSetEquivPoints W)) =
      Global.SupportDeformation.BundleCycles.globalSupportDeformationMap I (CycleClass.Geometric.GenericPoint.reducedSupportIdeal W)
        (genericPoint (Global.SupportDeformation.BundleCycles.globalSupportDeformation I (CycleClass.Geometric.GenericPoint.reducedSupportIdeal W))) := by
  let P := CycleClass.Geometric.GenericPoint.reducedSupportIdeal W
  let y := genericPoint (Support.LaurentChart.BundleCycles.supportPuncturedDeformation I P)
  have hp : Support.LaurentChart.BundleCycles.supportPuncturedMap I P y = Punctured.DeformationFlat.BundleCycles.puncturedFiberGenericPoint I (irreducibleSetEquivPoints W) :=
    (congrArg (Support.LaurentChart.BundleCycles.supportPuncturedMap I P) (Support.PuncturedFunctionField.BundleCycles.supportPuncturedGenericPoint_generic I P).symm).trans
      ((Support.LaurentNaturality.BundleCycles.supportPuncturedGenericPoint_toAmbient I P _).trans
        (congrArg (Punctured.DeformationFlat.BundleCycles.puncturedFiberGenericPoint I) (CycleClass.Geometric.GenericPoint.reducedSupport_genericPoint_eq W)))
  exact (congrArg (ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I) hp.symm).trans
    ((congrArg (fun k => k y) (Support.LaurentChart.BundleCycles.supportPuncturedMap_inclusion I P)).trans
      (congrArg (Global.SupportDeformation.BundleCycles.globalSupportDeformationMap I P) (genericPoint_eq_of_isOpenImmersion (Support.LaurentChart.BundleCycles.supportPuncturedInclusion I P))))

theorem supportDeformationImage_eq_pointClosure :
    CycleClass.Geometric.StratumClosure.integralImageClosure (Global.SupportDeformation.BundleCycles.globalSupportDeformationMap I (CycleClass.Geometric.GenericPoint.reducedSupportIdeal W)) =
      irreducibleSetEquivPoints.symm
        (ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I (Punctured.DeformationFlat.BundleCycles.puncturedFiberGenericPoint I (irreducibleSetEquivPoints W))) := by
  apply irreducibleSetEquivPoints.injective
  exact (Integral.ClosedImage.BundleCycles.integralClosedImage_genericPoint (Global.SupportDeformation.BundleCycles.globalSupportDeformationMap I (CycleClass.Geometric.GenericPoint.reducedSupportIdeal W))).trans
    ((puncturedGenericPoint_deformationInclusion I W).symm.trans (irreducibleSetEquivPoints.apply_symm_apply _).symm)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.SupportClosure.BundleCycles
