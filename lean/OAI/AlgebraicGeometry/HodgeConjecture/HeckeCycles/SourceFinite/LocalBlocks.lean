import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.IntrinsicActiveClosure
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ActiveFiniteMatrix

/-! # Local Blocks -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceFinite.LocalBlocks.CM

noncomputable section

/-! Continuous local matrix coordinates of the actual source finite
group, with exact rational values and supported active values. -/

open scoped Classical _root_.NumberField _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (Q : GeometricSource.CM.SymplecticCoordinates E B places)
  {q : ℕ} [Fact q.Prime] (f : E →+* ℚ_[q])

def localHom : Product.CM.FiniteGroup E Q →* Matrix.SpecialLinearGroup (Fin 3) ℚ_[q] :=
  (Source.QadicSpecialLinear.CM.equivalence E Q f).toMonoidHom.comp
    (RestrictedPlaceProduct.CM.evaluation (Product.CM.levels E Q)
      (Source.QadicPlace.CM.place E f))

theorem continuous : Continuous (localHom E Q f) :=
  (Source.QadicTopology.CM.equivalence_continuous E Q f).comp
    (RestrictedProduct.continuous_eval (Source.QadicPlace.CM.place E f))

theorem rational (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) :
    localHom E Q f (Source.RationalLocal.CM.finiteHom E Q g) =
      Matrix.SpecialLinearGroup.map f g.val :=
  Source.QadicSpecialLinear.CM.rational_map E Q f g

theorem active (g : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q]) :
    localHom E Q f (Source.ActiveFiniteMatrix.CM.active E Q f g) = g :=
  (congrArg (Source.QadicSpecialLinear.CM.equivalence E Q f)
    (Source.ActiveFiniteMatrix.CM.same E Q f g)).trans
      ((Source.QadicSpecialLinear.CM.equivalence E Q f).apply_symm_apply g)

theorem inactive (g : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q])
    (τ : E →+* ℚ_[q])
    (hτ : Source.QadicPlace.CM.place E τ ≠ Source.QadicPlace.CM.place E f) :
    localHom E Q τ (Source.ActiveFiniteMatrix.CM.active E Q f g) = 1 :=
  (congrArg (Source.QadicSpecialLinear.CM.equivalence E Q τ)
    (Source.ActiveFiniteMatrix.CM.other E Q f g hτ)).trans (map_one _)

variable {d : Gal(E/ℚ) → Bool} (L : GeometricSource.CM.LinePeriod E B places d)
  {I : Type*} (τ : I → E →+* ℚ_[q])

def blocks (a : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q] ×
    Source.FactorTheta.CM.RationalWeilFactorization.Away E L f) : I → Matrix.SpecialLinearGroup (Fin 3) ℚ_[q] :=
  fun i => localHom E (OppositeCoordinates.CM.coordinates E L.coordinates) (τ i)
    (Source.IntrinsicActiveClosure.CM.Intrinsic.assemble E L f a)

theorem blocks_continuous : Continuous (blocks E f L τ) :=
  continuous_pi (fun i => (continuous E (OppositeCoordinates.CM.coordinates E L.coordinates) (τ i)).comp
    (Source.IntrinsicActiveClosure.CM.Intrinsic.continuous E L f))

theorem blocks_rational (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) :
    blocks E f L τ (Source.RationalAwayTopology.CM.rational E L f g) =
      fun i => Matrix.SpecialLinearGroup.map (τ i) g.val := by
  funext i
  exact (congrArg (localHom E (OppositeCoordinates.CM.coordinates E L.coordinates) (τ i))
    (Source.IntrinsicActiveClosure.CM.Intrinsic.rational E L f g)).trans
      (rational E (OppositeCoordinates.CM.coordinates E L.coordinates) (τ i) g)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceFinite.LocalBlocks.CM
