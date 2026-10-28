import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ComponentBaseChange
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.EmbeddedAbelianVarieties
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ProjectiveAdapter
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GroupAmple

/-! # Concrete Complex Albanese Fibers -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! Construct native projective varieties on the literal complex
component fibers and their actual proper commutative group targets. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

def ConcreteComplexAlbaneseFibers.actualProperComplexGroupVariety (A : Over Foundations.Scheme.ProjectiveSpace.complexBase) [GrpObj A] [IsCommMonObj A]
    [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom] : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety := by
  have : ConnectedSpace A.left := GeometricallyConnected.connectedSpace_of_subsingleton A.hom
  exact {
    variety := ⟨{
      carrier := A.left
      structureMap := A.hom
      projective := AbelianModuli.ReferenceFamily.Intrinsic.ProjectiveAdapter.ProjectiveCoefficients.nativeProjectivePresentation
        (AbelianScheme.TateComparison.GroupAmple.properGroupProjectivePresentation A)
      smooth := inferInstance }, ArithmeticGeometry.Models.SpreadingOut.SmoothGeometricIntegrality.Construction.smooth_connected_scheme_integral A.hom⟩
    group := inferInstanceAs (GrpObj A)
    commutative := inferInstanceAs (IsCommMonObj A) }

variable {B : Scheme} {T : Over B} {r : ℕ} (D : Components.ComponentAlbaneseData T r)
    (c : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ B) (j : Fin r)

def Components.ComponentAlbaneseData.sourceComplexVariety
    [Smooth (D.S j).hom] [IsProper (D.S j).hom] [GeometricallyConnected (D.S j).hom]
    (hP : Components.RelativelyProjective (D.S j)) : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety := by
  let X := D.complexSurface c j
  have : Smooth X.hom := inferInstanceAs (Smooth (pullback.snd (D.S j).hom c))
  have : IsProper X.hom := inferInstanceAs (IsProper (pullback.snd (D.S j).hom c))
  have : GeometricallyConnected X.hom := inferInstanceAs (GeometricallyConnected (pullback.snd (D.S j).hom c))
  have : ConnectedSpace X.left := GeometricallyConnected.connectedSpace_of_subsingleton X.hom
  let P := AbelianModuli.ReferenceFamily.Intrinsic.ProjectiveAdapter.ProjectiveCoefficients.nativeProjectivePresentation
    (ComponentBaseChange.relativeProjectivePresentationBaseChange c (Classical.choice hP))
  exact ⟨⟨X.left, X.hom, P, inferInstance⟩, ArithmeticGeometry.Models.SpreadingOut.SmoothGeometricIntegrality.Construction.smooth_connected_scheme_integral X.hom⟩

def Components.ComponentAlbaneseData.targetComplexVariety
    [Smooth (D.A j).X.hom] [IsProper (D.A j).X.hom] [GeometricallyConnected (D.A j).X.hom] :
    ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety := by
  have : Smooth (D.complexAbelian c j).X.hom :=
    inferInstanceAs (Smooth (pullback.snd (D.A j).X.hom c))
  have : IsProper (D.complexAbelian c j).X.hom :=
    inferInstanceAs (IsProper (pullback.snd (D.A j).X.hom c))
  have : GeometricallyConnected (D.complexAbelian c j).X.hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd (D.A j).X.hom c))
  exact ConcreteComplexAlbaneseFibers.actualProperComplexGroupVariety (D.complexAbelian c j).X

theorem Components.ComponentAlbaneseData.native_complex_albanese
    [Smooth (D.S j).hom] [IsProper (D.S j).hom] [GeometricallyConnected (D.S j).hom]
    [Smooth (D.A j).X.hom] [IsProper (D.A j).X.hom] [GeometricallyConnected (D.A j).X.hom]
    (hP : Components.RelativelyProjective (D.S j)) (hA : D.IsComplexAlbanese c j) :
    Albanese.IsAlbaneseMap (D.sourceComplexVariety c j hP).presentation (D.complexBasePoint c j)
      (D.targetComplexVariety c j) (D.complexMap c j) := hA

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
