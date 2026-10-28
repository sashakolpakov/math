import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PELScalar
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.UnitaryFormHomeomorph
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RationalLocal
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.UnitaryHomeomorph
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SpecialUnitaryBaseChange

/-! # PEL Finite Group -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PELFiniteGroup.CM

/-! A continuous group equivalence identifies the actual source finite
unitary group with the PEL finite group and retains its rational matrices. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticForms.CM
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (Q : GeometricSource.CM.SymplecticCoordinates E B places)

def equivalence : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU (QuadraticConjugation.CM.Field.RealField E) (QuadraticForms.CM.hermitianForm E Q) ≃ₜ*
    RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (CMExtraction.UnitaryMatrixEquiv.Quadratic.diagonalForm (AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E B.b)) :=
  (CMExtraction.Finite.UnitaryHomeomorph.Approximation.finiteUnitaryCompletedHomeomorph (QuadraticConjugation.CM.Field.RealField E) (QuadraticForms.CM.hermitianForm E Q)).trans
    ((CMExtraction.SpecialUnitaryBaseChange.Approximation.specialUnitaryScalarHomeomorph (PELScalar.CM.equivalence E Q)
      (PELScalar.CM.conjugation E Q) _
      (PELScalar.CM.continuous E Q) (PELScalar.CM.inverse_continuous E Q)).trans
        (UnitaryFormHomeomorph.CM.equivalence _ _ (PELScalar.CM.hermitian E Q)))

theorem matrix (g : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU (QuadraticConjugation.CM.Field.RealField E) (QuadraticForms.CM.hermitianForm E Q)) :
    (equivalence E Q g).val.val =
      (CMExtraction.Finite.UnitaryDet.Approximation.finiteSUQuadraticMatrix (QuadraticConjugation.CM.Field.RealField E) (QuadraticForms.CM.hermitianForm E Q) g).map
        (PELScalar.CM.equivalence E Q) :=
  UnitaryFormHomeomorph.CM.matrix _ _ (PELScalar.CM.hermitian E Q) _

theorem rational_matrix (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) :
    (equivalence E Q (RationalLocal.CM.finiteHom E Q g)).val.val =
      g.val.val.map (AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E) := by
  rw [matrix]
  change (CMExtraction.Finite.UnitaryDet.Approximation.finiteSUQuadraticMatrix (QuadraticConjugation.CM.Field.RealField E) (QuadraticForms.CM.hermitianForm E Q)
    (RepresentationTheory.Theta.Adelic.RationalSU.rationalFiniteSU (QuadraticConjugation.CM.Field.RealField E) (QuadraticForms.CM.hermitianForm E Q)
      (UnitaryMatrix.CM.hom E Q g))).map (PELScalar.CM.equivalence E Q) = _
  rw [CMExtraction.Finite.UnitaryDet.Approximation.finiteSUQuadraticMatrix_rational]
  apply Matrix.ext
  intro i j
  exact (PELScalar.CM.rational E Q ((QuadraticConjugation.CM.Field.fieldEquiv E Q).symm (g.val.val i j))).trans
    (congrArg (AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E) ((QuadraticConjugation.CM.Field.fieldEquiv E Q).apply_symm_apply _))

variable {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hb : P.b = B.b)

def pel : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU (QuadraticConjugation.CM.Field.RealField E) (QuadraticForms.CM.hermitianForm E Q) ≃ₜ* P.FiniteSpecialUnitary :=
  (equivalence E Q).trans
    ((UnitaryFormHomeomorph.CM.equivalence _ _
      (congrArg (fun b : E => CMExtraction.UnitaryMatrixEquiv.Quadratic.diagonalForm (AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E b)) hb.symm)).trans
        (CMExtraction.UnitaryLinear.Approximation.matrixPELUnitaryHomeomorph E P))

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PELFiniteGroup.CM

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PELFiniteGroup.CM.Matrix

/-! The PEL image of the actual source finite group retains its full
matrix, including its action on every rational vector. -/

open scoped Classical _root_.NumberField _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticForms.CM
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz

open _root_.Matrix

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (Q : GeometricSource.CM.SymplecticCoordinates E B places)
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hb : P.b = B.b)

theorem entry (g : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU (QuadraticConjugation.CM.Field.RealField E) (QuadraticForms.CM.hermitianForm E Q)) (i j : Fin 3) :
    (pel E Q P hb g).val (Pi.single j 1) i =
      (equivalence E Q g).val.val i j :=
  (CMExtraction.UnitaryLinear.Approximation.matrixPELUnitary_entry E P _ i j).trans
    (congrArg (fun M : Matrix (Fin 3) (Fin 3) (AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) => M i j)
      (UnitaryFormHomeomorph.CM.matrix _ _
        (congrArg (fun b : E => CMExtraction.UnitaryMatrixEquiv.Quadratic.diagonalForm (AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E b)) hb.symm)
        (equivalence E Q g)))

theorem rational_matrix (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) :
    LinearMap.toMatrix' (pel E Q P hb
      (RationalLocal.CM.finiteHom E Q g)).val.toLinearMap =
        g.val.val.map (AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E) := by
  apply Matrix.ext
  intro i j
  exact (entry E Q P hb _ i j).trans
    (congrArg (fun M : Matrix (Fin 3) (Fin 3) (AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) => M i j)
      (CM.rational_matrix E Q g))

theorem rational_vector (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (x : Fin 3 → E) :
    (pel E Q P hb
      (RationalLocal.CM.finiteHom E Q g)).val (AbelianModuli.ReferenceFamily.AdelicData.finiteVectorEmbedding E x) =
        AbelianModuli.ReferenceFamily.AdelicData.finiteVectorEmbedding E (g.val.val *ᵥ x) := by
  have hm := congrArg (fun M : Matrix (Fin 3) (Fin 3) (AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) =>
    M *ᵥ AbelianModuli.ReferenceFamily.AdelicData.finiteVectorEmbedding E x) (rational_matrix E Q P hb g)
  exact (LinearMap.toMatrix'_mulVec
    (pel E Q P hb
      (RationalLocal.CM.finiteHom E Q g)).val.toLinearMap
    (AbelianModuli.ReferenceFamily.AdelicData.finiteVectorEmbedding E x)).symm.trans
      (hm.trans (funext (fun i =>
        (RingHom.map_mulVec (AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E).toRingHom g.val.val x i).symm)))

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PELFiniteGroup.CM.Matrix

end

end OAI
