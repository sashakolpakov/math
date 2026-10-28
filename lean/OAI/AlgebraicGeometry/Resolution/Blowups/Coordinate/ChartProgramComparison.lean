import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.SubspaceChartModel
import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.ProgramCenterPattern

/-! # Chart Program Comparison -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.ChartProgramComparison.Construction

noncomputable section

/-! A chart comparison retains its actual common program and the empty-until-whole behavior of its coordinate model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

structure CoordinateChartProgramComparison
    {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData}
    (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix 1 X f J Y g K) {x : X} (C : Global.CoordinateSubspaceChart.Construction.GlobalCoordinateSubspaceChart f J x) where
  modelEndpoint : Scheme
  modelStructureMap : modelEndpoint ⟶ Foundations.Scheme.ProjectiveSpace.complexBase
  modelTerminalIdeal : modelEndpoint.IdealSheafData
  modelProgram : Smooth.ControlPrefix.Construction.SmoothControlPrefix 1 C.modelScheme C.modelStructure C.modelIdeal
    modelEndpoint modelStructureMap modelTerminalIdeal
  modelPattern : modelProgram.UnitUntilWhole
  commonEndpoint : Scheme
  commonStructureMap : commonEndpoint ⟶ Foundations.Scheme.ProjectiveSpace.complexBase
  commonTerminalIdeal : commonEndpoint.IdealSheafData
  commonProgram : Smooth.ControlPrefix.Construction.SmoothControlPrefix 1 (Spec C.ring) (C.map ≫ f) (J.comap C.map)
    commonEndpoint commonStructureMap commonTerminalIdeal
  globalMap : commonEndpoint ⟶ Y
  globalComparison : P.EtaleComparison commonProgram C.map globalMap
  modelMap : commonEndpoint ⟶ modelEndpoint
  modelComparison : modelProgram.EtaleComparison commonProgram C.modelMap modelMap

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.ChartProgramComparison.Construction
