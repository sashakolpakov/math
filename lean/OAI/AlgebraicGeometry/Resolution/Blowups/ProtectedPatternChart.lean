import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.ProgramCenterPattern
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.InitialComparison

/-! # Protected Pattern Chart -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ProtectedPatternChart.Construction

noncomputable section

/-! Protected program covers retain common actual programs, marked points, and model center patterns through later blowup steps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

structure ProtectedPatternProgramChart
    {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData}
    (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix 1 X f J Y g K) (O : X.Opens) where
  source : Scheme
  structureMap : source ⟶ Foundations.Scheme.ProjectiveSpace.complexBase
  ideal : source.IdealSheafData
  integral : IsIntegral source
  noetherian : IsLocallyNoetherian source
  point : source
  pointMarked : point ∈ ideal.support
  map : source ⟶ X
  isOpenImmersion : IsOpenImmersion map
  contained : ∀ y, map y ∈ O
  modelSource : Scheme
  modelStructureMap : modelSource ⟶ Foundations.Scheme.ProjectiveSpace.complexBase
  modelIdeal : modelSource.IdealSheafData
  modelIntegral : IsIntegral modelSource
  modelNoetherian : IsLocallyNoetherian modelSource
  modelEndpoint : Scheme
  modelEndStructureMap : modelEndpoint ⟶ Foundations.Scheme.ProjectiveSpace.complexBase
  modelEndIdeal : modelEndpoint.IdealSheafData
  modelProgram : Smooth.ControlPrefix.Construction.SmoothControlPrefix 1 modelSource modelStructureMap modelIdeal
    modelEndpoint modelEndStructureMap modelEndIdeal
  modelPattern : modelProgram.UnitUntilWhole
  commonEndpoint : Scheme
  commonEndStructureMap : commonEndpoint ⟶ Foundations.Scheme.ProjectiveSpace.complexBase
  commonEndIdeal : commonEndpoint.IdealSheafData
  commonProgram : Smooth.ControlPrefix.Construction.SmoothControlPrefix 1 source structureMap ideal
    commonEndpoint commonEndStructureMap commonEndIdeal
  globalEndMap : commonEndpoint ⟶ Y
  globalComparison : P.EtaleComparison commonProgram map globalEndMap
  modelMap : source ⟶ modelSource
  modelEndMap : commonEndpoint ⟶ modelEndpoint
  modelComparison : modelProgram.EtaleComparison commonProgram modelMap modelEndMap

attribute [instance] ProtectedPatternProgramChart.integral ProtectedPatternProgramChart.noetherian
  ProtectedPatternProgramChart.isOpenImmersion ProtectedPatternProgramChart.modelIntegral
  ProtectedPatternProgramChart.modelNoetherian

structure ProtectedPatternProgramCover
    {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData}
    (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix 1 X f J Y g K) (O : X.Opens) where
  indices : Type
  chart : indices → ProtectedPatternProgramChart P O
  cover : ∀ x ∈ J.support, x ∈ O → ∃ i y, (chart i).map y = x

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ProtectedPatternChart.Construction
