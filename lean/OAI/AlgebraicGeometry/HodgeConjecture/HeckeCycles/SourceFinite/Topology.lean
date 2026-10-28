import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceFinite.Product
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QadicTopology
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.RestrictedPlaceProduct

/-! # Topology -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceFinite.Topology.CM

noncomputable section

/-! The source's local/away presentation has the actual product topology. -/

open scoped Classical _root_.Matrix _root_.NumberField
open _root_.Matrix OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QadicPlace.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceFinite.Product.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (Q : GeometricSource.CM.SymplecticCoordinates E B places)
  {q : ℕ} [Fact q.Prime] (f : E →+* ℚ_[q])

instance levels_open : Fact (∀ v, IsOpen (Product.CM.levels E Q v : Set
    (RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm (Source.QuadraticConjugation.CM.Field.RealField E)
      (Source.QuadraticForms.CM.hermitianForm E Q).val (.inr v))))) :=
  ⟨fun v => RepresentationTheory.Theta.Adelic.IntegralTopology.localSUIntegral_open (Source.QuadraticConjugation.CM.Field.RealField E)
    (Source.QuadraticForms.CM.hermitianForm E Q).val (.inr v)⟩

def homeomorphism : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q] × Product.CM.Away E Q f ≃ₜ Product.CM.FiniteGroup E Q :=
  ((Source.QadicTopology.CM.homeomorphism E Q f).symm.prodCongr (Homeomorph.refl _)).trans
    (RestrictedPlaceProduct.CM.Topology.homeomorphism (Product.CM.levels E Q) (Source.QadicPlace.CM.place E f))

theorem homeomorphism_apply (x : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q] × Product.CM.Away E Q f) :
    homeomorphism E Q f x = Product.CM.equivalence E Q f x := rfl

theorem equivalence_continuous : Continuous (Product.CM.equivalence E Q f) := (homeomorphism E Q f).continuous

theorem inverse_continuous : Continuous (Product.CM.equivalence E Q f).symm := (homeomorphism E Q f).symm.continuous

theorem rational_factorization (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) :
    homeomorphism E Q f (Matrix.SpecialLinearGroup.map f g.val, Product.CM.awayHom E Q f g) =
      Source.RationalLocal.CM.finiteHom E Q g :=
  Product.CM.rational_factorization E Q f g

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceFinite.Topology.CM
