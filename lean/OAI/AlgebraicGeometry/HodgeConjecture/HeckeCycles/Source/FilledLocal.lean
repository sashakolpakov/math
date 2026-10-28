import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PELFiniteGroup
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PELPadic
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceFinite.Product
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.RestrictedFillComparison

/-! # Filled Local -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FilledLocal.CM.PEL

/-! The actual rational PEL operator with its chosen local unitary
factor replaced by the identity. -/

open scoped Classical _root_.NumberField _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticForms.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (Q : GeometricSource.CM.SymplecticCoordinates E B places)
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hb : P.b = B.b)
  {q : ℕ} [Fact q.Prime] (f : E →+* ℚ_[q])

def fill : SourceFinite.Product.CM.FiniteGroup E Q →* SourceFinite.Product.CM.FiniteGroup E Q :=
  RestrictedFillComparison.CM.fill (SourceFinite.Product.CM.levels E Q) (QadicPlace.CM.place E f)

def hom : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b →* P.FiniteSpecialUnitary :=
  (PELFiniteGroup.CM.pel E Q P hb).toMulEquiv.toMonoidHom.comp
    ((fill E Q f).comp (RationalLocal.CM.finiteHom E Q))

theorem matrix_entry (g : SourceFinite.Product.CM.FiniteGroup E Q) (i j : Fin 3) :
    (PELFiniteGroup.CM.pel E Q P hb (fill E Q f g)).val (Pi.single j 1) i =
      PELScalar.CM.equivalence E Q
        (CMExtraction.Finite.UnitaryDet.Approximation.finiteSUQuadraticMatrix (QuadraticConjugation.CM.Field.RealField E) (QuadraticForms.CM.hermitianForm E Q) (fill E Q f g) i j) :=
  (PELFiniteGroup.CM.Matrix.entry E Q P hb _ i j).trans
    (congrArg (fun M : Matrix (Fin 3) (Fin 3) (AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) => M i j)
      (PELFiniteGroup.CM.matrix E Q (fill E Q f g)))

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FilledLocal.CM.PEL

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FilledLocal.CM

/-! The filled source PEL operator is the identity at the omitted place
and retains the original rational matrix at every other local place. -/

open scoped Classical _root_.NumberField _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticForms.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (Q : GeometricSource.CM.SymplecticCoordinates E B places)
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hb : P.b = B.b)
  {q : ℕ} [Fact q.Prime] (f : E →+* ℚ_[q])
  {p : ℕ} [Fact p.Prime] (τ : E →+* ℚ_[p])

theorem entry (g : SourceFinite.Product.CM.FiniteGroup E Q) (i j : Fin 3) :
    CMExtraction.Finite.CoefficientPadic.TestTransport.finiteCoefficientPadic E τ
      ((PELFiniteGroup.CM.pel E Q P hb (PEL.fill E Q f g)).val (Pi.single j 1) i) =
    (QadicSpecialLinear.CM.equivalence E Q τ
      (PEL.fill E Q f g (QadicPlace.CM.place E τ))).val i j :=
  (congrArg (CMExtraction.Finite.CoefficientPadic.TestTransport.finiteCoefficientPadic E τ) (PELFiniteGroup.CM.Matrix.entry E Q P hb _ i j)).trans
    (congrArg (fun M : Matrix (Fin 3) (Fin 3) ℚ_[p] => M i j)
      (PELPadic.CM.matrix E Q τ (PEL.fill E Q f g)))

theorem same (hplace : QadicPlace.CM.place E τ = QadicPlace.CM.place E f)
    (g : SourceFinite.Product.CM.FiniteGroup E Q) (i j : Fin 3) :
    CMExtraction.Finite.CoefficientPadic.TestTransport.finiteCoefficientPadic E τ
      ((PELFiniteGroup.CM.pel E Q P hb (PEL.fill E Q f g)).val (Pi.single j 1) i) =
      (1 : Matrix (Fin 3) (Fin 3) ℚ_[p]) i j := by
  have he : PEL.fill E Q f g (QadicPlace.CM.place E τ) = 1 :=
    Eq.mpr (congrArg (fun v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace (QuadraticConjugation.CM.Field.RealField E) =>
      PEL.fill E Q f g v = 1) hplace)
      (RestrictedFillComparison.CM.same (SourceFinite.Product.CM.levels E Q)
        (QadicPlace.CM.place E f) g)
  exact (entry E Q P hb f τ g i j).trans
    (congrArg (fun u : Matrix.SpecialLinearGroup (Fin 3) ℚ_[p] => u.val i j)
      ((congrArg (QadicSpecialLinear.CM.equivalence E Q τ) he).trans (map_one _)))

theorem rational_other (hplace : QadicPlace.CM.place E τ ≠ QadicPlace.CM.place E f)
    (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (i j : Fin 3) :
    CMExtraction.Finite.CoefficientPadic.TestTransport.finiteCoefficientPadic E τ ((PEL.hom E Q P hb f g).val (Pi.single j 1) i) =
      τ (g.val.val i j) := by
  have he := RestrictedFillComparison.CM.other (SourceFinite.Product.CM.levels E Q)
    (QadicPlace.CM.place E f) (RationalLocal.CM.finiteHom E Q g) hplace
  exact (entry E Q P hb f τ (RationalLocal.CM.finiteHom E Q g) i j).trans
    (congrArg (fun u : Matrix.SpecialLinearGroup (Fin 3) ℚ_[p] => u.val i j)
      ((congrArg (QadicSpecialLinear.CM.equivalence E Q τ) he).trans
        (QadicSpecialLinear.CM.rational_map E Q τ g)))

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FilledLocal.CM

end

end OAI
