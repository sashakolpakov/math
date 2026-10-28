import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QadicSpecialLinear
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QadicCompletionIntegers
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SplitIntegralLocal
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IntegralCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.PlaceExclusion

/-! # Qadic Integral -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QadicIntegral.CM

noncomputable section

/-! Standard integral SL3 matrices lie in the native integral unitary
subgroup at every source place outside one finite exceptional set. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticForms.CM
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary.SplitAlgebra

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QadicPlace.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QadicSpecialLinear.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (Q : GeometricSource.CM.SymplecticCoordinates E B places)
  {q : ℕ} [Fact q.Prime] (f : E →+* ℚ_[q])

local instance : CharZero (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion (QuadraticConjugation.CM.Field.RealField E) (.inr (QadicPlace.CM.place E f))) :=
  RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.completionCharZero (QuadraticConjugation.CM.Field.RealField E) (.inr (QadicPlace.CM.place E f))

theorem plus_integral (g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (QadicSpecialLinear.CM.localForm E Q f).val)
    (hg : QadicSpecialLinear.CM.equivalence E Q f g ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) :
    ∀ i j, RepresentationTheory.Theta.Adelic.SpecialUnitary.SplitAlgebra.plus (QadicPlace.CM.root E Q f) (QadicPlace.CM.root_sq E Q f) (QadicPlace.CM.root_ne_zero E Q f) (g.val.val i j) ∈
      RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localIntegerRing (QuadraticConjugation.CM.Field.RealField E) (.inr (QadicPlace.CM.place E f)) := by
  intro i j
  exact (QadicCompletionIntegers.CM.integral_iff (QadicPlace.CM.realEmbedding E f) _).mpr
    ((CMExtraction.IntegralCoordinates.TestTransport.integralSL3_iff_entries q (QadicSpecialLinear.CM.equivalence E Q f g)).mp hg i j)

theorem local_integral
    (hgood : SplitIntegralLocal.CM.Good (QuadraticConjugation.CM.Field.RealField E) (QuadraticForms.CM.hermitianForm E Q) (QadicPlace.CM.place E f))
    (g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (QadicSpecialLinear.CM.localForm E Q f).val)
    (hg : QadicSpecialLinear.CM.equivalence E Q f g ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) :
    g ∈ RepresentationTheory.Theta.Adelic.IntegralTopology.localSUIntegral
      (QuadraticConjugation.CM.Field.RealField E) (QuadraticForms.CM.hermitianForm E Q).val (.inr (QadicPlace.CM.place E f)) := by
  apply SplitIntegralLocal.CM.integral (QuadraticConjugation.CM.Field.RealField E) (QuadraticForms.CM.hermitianForm E Q)
    (QadicPlace.CM.place E f) hgood (QadicPlace.CM.root E Q f) (QadicPlace.CM.root_sq E Q f) (QadicPlace.CM.root_ne_zero E Q f)
    (QadicSpecialLinear.CM.local_hermitian E Q f) g (plus_integral E Q f g hg)
  apply plus_integral E Q f g⁻¹
  rw [map_inv]
  exact (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q).inv_mem hg

theorem inverse_integral
    (hgood : SplitIntegralLocal.CM.Good (QuadraticConjugation.CM.Field.RealField E) (QuadraticForms.CM.hermitianForm E Q) (QadicPlace.CM.place E f))
    (u : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q) (hu : u ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) :
    (QadicSpecialLinear.CM.equivalence E Q f).symm u ∈ RepresentationTheory.Theta.Adelic.IntegralTopology.localSUIntegral
      (QuadraticConjugation.CM.Field.RealField E) (QuadraticForms.CM.hermitianForm E Q).val (.inr (QadicPlace.CM.place E f)) :=
  local_integral E Q f hgood _ (((QadicSpecialLinear.CM.equivalence E Q f).apply_symm_apply u).symm ▸ hu)

theorem exists_good_bound :
    ∃ N : ℕ, 0 < N ∧ ∀ (p : ℕ) [Fact p.Prime], Nat.Coprime p N →
      ∀ τ : E →+* ℚ_[p],
        SplitIntegralLocal.CM.Good (QuadraticConjugation.CM.Field.RealField E) (QuadraticForms.CM.hermitianForm E Q) (QadicPlace.CM.place E τ) :=
  Finite.PlaceExclusion.CM.exists_embedding_bound (QuadraticConjugation.CM.Field.RealField E) (algebraMap (QuadraticConjugation.CM.Field.RealField E) E) _
    (SplitIntegralLocal.CM.cofinite (QuadraticConjugation.CM.Field.RealField E) (QuadraticForms.CM.hermitianForm E Q))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QadicIntegral.CM
