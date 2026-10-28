import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.ChartProgramComparison
import OAI.AlgebraicGeometry.Resolution.Blowups.ProtectedPatternChart

/-! # Comparison Protected Chart -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate

noncomputable section

/-! Retained coordinate comparisons give pointed protected pattern charts with exact marked inputs. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def ChartProgramComparison.Construction.CoordinateChartProgramComparison.toProtectedChart
    {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData}
    {P : Smooth.ControlPrefix.Construction.SmoothControlPrefix 1 X f J Y g K} {x : X} {C : Global.CoordinateSubspaceChart.Construction.GlobalCoordinateSubspaceChart f J x}
    (A : ChartProgramComparison.Construction.CoordinateChartProgramComparison P C) (O : X.Opens) (hx : x ∈ J.support)
    (hO : ∀ p, C.map p ∈ O) : ProtectedPatternChart.Construction.ProtectedPatternProgramChart P O := by
  let : IsNoetherianRing C.ring := Algebra.FiniteType.isNoetherianRing ℂ C.ring
  refine { source := Spec C.ring
           structureMap := C.map ≫ f
           ideal := J.comap C.map
           integral := inferInstance
           noetherian := inferInstance
           point := C.point
           pointMarked := ?_
           map := C.map
           isOpenImmersion := inferInstance
           contained := hO
           modelSource := C.modelScheme
           modelStructureMap := C.modelStructure
           modelIdeal := C.modelIdeal
           modelIntegral := inferInstance
           modelNoetherian := inferInstance
           modelEndpoint := A.modelEndpoint
           modelEndStructureMap := A.modelStructureMap
           modelEndIdeal := A.modelTerminalIdeal
           modelProgram := A.modelProgram
           modelPattern := A.modelPattern
           commonEndpoint := A.commonEndpoint
           commonEndStructureMap := A.commonStructureMap
           commonEndIdeal := A.commonTerminalIdeal
           commonProgram := A.commonProgram
           globalEndMap := A.globalMap
           globalComparison := A.globalComparison
           modelMap := C.modelMap
           modelEndMap := A.modelMap
           modelComparison := A.modelComparison }
  rw [Scheme.IdealSheafData.support_comap]
  change C.map C.point ∈ J.support
  rwa [C.point_over]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate
