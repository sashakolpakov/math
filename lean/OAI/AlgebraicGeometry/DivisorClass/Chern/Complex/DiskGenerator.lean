import OAI.AlgebraicGeometry.DivisorClass.Chern.PlaneDiskBoundary
import OAI.AlgebraicGeometry.DivisorClass.Chern.OrthantCircleNormalization
import OAI.AlgebraicGeometry.DivisorClass.Chern.CircleNormalFilling

/-! # Disk Generator -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Complex.DiskGenerator

noncomputable section

/-!
# ChernClass: a supported disk representative of the original complex normal generator

The two half-plane fillings are carried into the original complex normal
line by its inverse ordered real coordinates. Their exact boundary and
the previously computed circle coordinate prove that this relative
two-cycle is the specified geometric generator.
-/

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def planeToNormalLine : TopCat.of PlaneHalf.CoordinatePlane ⟶ NormalWinding.windingNormalLine :=
  TopCat.ofHom ⟨(CycleClass.Geometric.RealComplexNormalModel.Cycles.complexRealEuclideanEquiv 1).symm, (CycleClass.Geometric.RealComplexNormalModel.Cycles.complexRealEuclideanEquiv 1).symm.continuous⟩

theorem planeSphereInclusion_normalLine :
    PlaneDiskBoundary.planeSphereInclusion ≫ planeToNormalLine =
      CircleNormalMap.circleToNormalPunctured ≫ CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured := by
  apply TopCat.ext
  intro x
  change (CycleClass.Geometric.RealComplexNormalModel.Cycles.complexRealEuclideanEquiv 1).symm x.val = CircleNormalMap.circleNormalCoordinate x
  apply (CycleClass.Geometric.RealComplexNormalModel.Cycles.complexRealEuclideanEquiv 1).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, CircleNormalMap.circleNormalCoordinate_real]

def normalOrthantCircleCycle :
    AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of NormalWinding.windingNormalPunctured)) 1 :=
  AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map CircleNormalMap.circleToNormalPunctured) 1 (OrthantSphereCycle.orientedOrthantSphereCycle 1)

def normalSupportedDiskFilling : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains NormalWinding.windingNormalLine).X 2 :=
  (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map planeToNormalLine).f 2 PlaneDiskBoundary.planeDiskFilling

theorem normalSupportedDiskFilling_boundary :
    (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains NormalWinding.windingNormalLine).d 2 1 normalSupportedDiskFilling =
      (CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured).f 1 normalOrthantCircleCycle.val := by
  have h := ConcreteCategory.congr_hom
    ((CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map planeToNormalLine).comm 2 1) PlaneDiskBoundary.planeDiskFilling
  change _ = (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map planeToNormalLine).f 1
    ((CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of PlaneHalf.CoordinatePlane)).d 2 1 PlaneDiskBoundary.planeDiskFilling) at h
  rw [PlaneDiskBoundary.planeDiskFilling_boundary] at h
  refine h.trans ?_
  have hm := congrArg (fun f => f.f 1) (congrArg CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map
    planeSphereInclusion_normalLine)
  rw [CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map_comp, CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map_comp] at hm
  exact ConcreteCategory.congr_hom hm (OrthantSphereCycle.orientedOrthantSphereChain 1)

def normalSupportedDiskRelativeCycle :
    AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured) 2 :=
  ⟨(CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured).f 2 normalSupportedDiskFilling,
    IntegralResidueEvaluation.integralRelativeProjection_cycle_of_boundary NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured
      normalSupportedDiskFilling normalOrthantCircleCycle.val normalSupportedDiskFilling_boundary⟩

def normalSupportedDiskRelativeClass : CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured 2 :=
  AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured) 2 normalSupportedDiskRelativeCycle

theorem normalSupportedDiskRelativeClass_boundary :
    CycleClass.Geometric.RelativeHomologyExact.Cycles.relativeHomologyBoundary NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured 1 normalSupportedDiskRelativeClass =
      AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of NormalWinding.windingNormalPunctured)) 1 normalOrthantCircleCycle :=
  AlgebraicTopology.Duality.Poincare.ConnectingRepresentatives.homologyConnecting_eq_of_lift (CycleClass.Geometric.LocalHomology.Cycles.relativeChainSequence NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured)
    (CycleClass.Geometric.LocalHomology.Cycles.relativeChainSequence_shortExact NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured) 1
    normalSupportedDiskRelativeCycle normalSupportedDiskFilling normalOrthantCircleCycle
    rfl normalSupportedDiskFilling_boundary.symm

theorem normalSupportedDiskRelativeClass_realSphere :
    (CycleClass.Geometric.RealComplexNormalModel.Cycles.complexNormalLocalRealSphereIso 1 1 (by decide)).hom normalSupportedDiskRelativeClass =
      OrthantSphereCycle.orientedOrthantSphereClass 1 := by
  rw [CycleClass.Geometric.RealComplexNormalModel.Cycles.complexNormalLocalRealSphereIso_hom]
  change CycleClass.Geometric.RelativeHomologyExact.Cycles.integralSingularHomologyMap (TopCat.ofHom (CycleClass.Geometric.RealComplexNormalModel.Cycles.complexRealSphereHomotopyEquiv 1).toFun) 1
    (CycleClass.Geometric.RelativeHomologyExact.Cycles.integralSingularHomologyMap (TopCat.ofHom (CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection (Fin 1 → ℂ))) 1
      (CycleClass.Geometric.RelativeHomologyExact.Cycles.relativeHomologyBoundary NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured 1 normalSupportedDiskRelativeClass)) = _
  rw [normalSupportedDiskRelativeClass_boundary]
  have hc : CycleClass.Geometric.RelativeHomologyExact.Cycles.integralSingularHomologyMap CircleNormalMap.circleToNormalPunctured 1 (OrthantSphereCycle.orientedOrthantSphereClass 1) =
      AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of NormalWinding.windingNormalPunctured)) 1 normalOrthantCircleCycle :=
    AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainClass_naturality (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map CircleNormalMap.circleToNormalPunctured) 1
      (OrthantSphereCycle.orientedOrthantSphereCycle 1)
  rw [← hc]
  have hm : CycleClass.Geometric.RelativeHomologyExact.Cycles.integralSingularHomologyMap CircleNormalMap.circleToNormalPunctured 1 ≫
      CycleClass.Geometric.RelativeHomologyExact.Cycles.integralSingularHomologyMap (TopCat.ofHom (CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection (Fin 1 → ℂ))) 1 ≫
      CycleClass.Geometric.RelativeHomologyExact.Cycles.integralSingularHomologyMap (TopCat.ofHom (CycleClass.Geometric.RealComplexNormalModel.Cycles.complexRealSphereHomotopyEquiv 1).toFun) 1 =
      𝟙 (CycleClass.Geometric.RelativeHomologyExact.Cycles.integralSingularHomology CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle 1) := by
    simp only [CycleClass.Geometric.RelativeHomologyExact.Cycles.integralSingularHomologyMap, ← HomologicalComplex.homologyMap_comp,
      ← CategoryTheory.Functor.map_comp, CircleNormalMap.circleToNormalPunctured_real_radial]
    rw [CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map_id, HomologicalComplex.homologyMap_id]
  exact ConcreteCategory.congr_hom hm (OrthantSphereCycle.orientedOrthantSphereClass 1)

theorem normalSupportedDiskRelativeClass_eq_originalGenerator :
    normalSupportedDiskRelativeClass = (CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso 1).inv 1 := by
  apply (CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso 1).toLinearEquiv.injective
  change (CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso 1).hom normalSupportedDiskRelativeClass =
    (CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso 1).hom ((CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso 1).inv 1)
  rw [Iso.inv_hom_id_apply]
  change CycleClass.Geometric.SphereHomologyInduction.Cycles.standardCircleH1Iso.hom
    ((CycleClass.Geometric.RealComplexNormalModel.Cycles.complexNormalLocalRealSphereIso 1 1 (by decide)).hom normalSupportedDiskRelativeClass) = 1
  rw [normalSupportedDiskRelativeClass_realSphere]
  exact OrthantCircleNormalization.orientedOrthantCircle_coordinate

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Complex.DiskGenerator
