import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RealCoefficients
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.DiagonalFrame
import OAI.RepresentationTheory.Weil.AdelicSplitting.Assembly

/-! # Global Frames -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.GlobalFrames.CM

noncomputable section

/-! An explicit rational polarization and all of its local realizations
for the source's actual Hermitian space and multiplicity line. -/

open scoped Classical _root_.Matrix
open _root_.Matrix OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticForms.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RealCoefficients.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (C : GeometricSource.CM.SymplecticCoordinates E B places)

def rational : RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.SymplecticFrame (QuadraticConjugation.CM.Field.discriminant E C) 3 1 (QuadraticForms.CM.hermitianForm E C).val (QuadraticForms.CM.skewForm E C).val where
  coordinates := DiagonalFrame.CM.Symplectic.coordinates (QuadraticConjugation.CM.Field.discriminant E C)
    (RealCoefficients.CM.skewCoefficient E C) (RealCoefficients.CM.hermitianCoefficient E (B := B))
    (QuadraticConjugation.CM.Field.discriminant_ne_zero E C) (RealCoefficients.CM.skewCoefficient_ne_zero E C)
    (RealCoefficients.CM.hermitianCoefficient_ne_zero E (B := B))
  preserves := by
    intro x y
    rw [RealCoefficients.CM.hermitian_form, RealCoefficients.CM.skew_form]
    exact DiagonalFrame.CM.TracePairing.preserves _ _ _ x y

def scalar (v : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places (QuadraticConjugation.CM.Field.RealField E)) := RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar (QuadraticConjugation.CM.Field.RealField E) v

theorem local_hermitian (v : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places (QuadraticConjugation.CM.Field.RealField E)) :
    (RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.localizedUnit (QuadraticConjugation.CM.Field.RealField E) (QuadraticConjugation.CM.Field.discriminant E C) (QuadraticForms.CM.hermitianForm E C) v).val =
      DiagonalFrame.CM.Symplectic.hermitian (scalar E v (QuadraticConjugation.CM.Field.discriminant E C))
        (fun i => scalar E v (RealCoefficients.CM.hermitianCoefficient E (B := B) i)) := by
  change (QuadraticForms.CM.hermitianForm E C).val.map (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange (scalar E v) (QuadraticConjugation.CM.Field.discriminant E C)) = _
  rw [RealCoefficients.CM.hermitian_form]
  exact DiagonalFrame.CM.BaseChange.hermitian_map _ _ _

theorem local_skew (v : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places (QuadraticConjugation.CM.Field.RealField E)) :
    (RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.localizedUnit (QuadraticConjugation.CM.Field.RealField E) (QuadraticConjugation.CM.Field.discriminant E C) (QuadraticForms.CM.skewForm E C) v).val =
      DiagonalFrame.CM.Symplectic.skew (scalar E v (QuadraticConjugation.CM.Field.discriminant E C))
        (scalar E v (RealCoefficients.CM.skewCoefficient E C)) := by
  change (QuadraticForms.CM.skewForm E C).val.map (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange (scalar E v) (QuadraticConjugation.CM.Field.discriminant E C)) = _
  rw [RealCoefficients.CM.skew_form]
  exact DiagonalFrame.CM.BaseChange.skew_map _ _ _

def localFrame (v : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places (QuadraticConjugation.CM.Field.RealField E)) :
    RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.SymplecticFrame (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar (QuadraticConjugation.CM.Field.RealField E) v (QuadraticConjugation.CM.Field.discriminant E C)) 3 1
      (RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.localizedUnit (QuadraticConjugation.CM.Field.RealField E) (QuadraticConjugation.CM.Field.discriminant E C) (QuadraticForms.CM.hermitianForm E C) v).val
      (RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.localizedUnit (QuadraticConjugation.CM.Field.RealField E) (QuadraticConjugation.CM.Field.discriminant E C) (QuadraticForms.CM.skewForm E C) v).val where
  coordinates := DiagonalFrame.CM.Symplectic.coordinates (scalar E v (QuadraticConjugation.CM.Field.discriminant E C))
    (scalar E v (RealCoefficients.CM.skewCoefficient E C))
    (fun i => scalar E v (RealCoefficients.CM.hermitianCoefficient E (B := B) i))
    ((map_ne_zero (scalar E v)).mpr (QuadraticConjugation.CM.Field.discriminant_ne_zero E C))
    ((map_ne_zero (scalar E v)).mpr (RealCoefficients.CM.skewCoefficient_ne_zero E C))
    (fun i => (map_ne_zero (scalar E v)).mpr (RealCoefficients.CM.hermitianCoefficient_ne_zero E i))
  preserves := by
    intro x y
    rw [local_hermitian, local_skew]
    exact DiagonalFrame.CM.TracePairing.preserves _ _ _ x y

theorem compatible (v : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places (QuadraticConjugation.CM.Field.RealField E))
    (x : RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition (QuadraticConjugation.CM.Field.discriminant E C) 3 1) (i : Fin (3 * 1) ⊕ Fin (3 * 1)) :
    (CM.localFrame E C v).coordinates (fun j => RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal (QuadraticConjugation.CM.Field.RealField E) (QuadraticConjugation.CM.Field.discriminant E C) v (x j)) i =
      RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar (QuadraticConjugation.CM.Field.RealField E) v ((CM.rational E C).coordinates x i) :=
  DiagonalFrame.CM.BaseChange.forward_map (scalar E v) (QuadraticConjugation.CM.Field.discriminant E C)
    (RealCoefficients.CM.skewCoefficient E C) (RealCoefficients.CM.hermitianCoefficient E (B := B)) x i

def frames : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.GlobalFrames (QuadraticConjugation.CM.Field.RealField E) (QuadraticConjugation.CM.Field.discriminant E C) 3 1 (QuadraticForms.CM.hermitianForm E C) (QuadraticForms.CM.skewForm E C) where
  rational := CM.rational E C
  localFrame := CM.localFrame E C
  coordinates_compatible := compatible E C

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.GlobalFrames.CM
