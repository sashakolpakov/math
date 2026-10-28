import OAI.RepresentationTheory.Theta.Adelic.DataTheta

/-! # Theta Rational Complex Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.ThetaRationalComplexComparison.CM

noncomputable section

/-! AdelicTheta's real and complex coordinate conclusions identify every actual
rational tensor vector with its CM components. -/

open scoped Classical _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.BallGeometryData

variable (F : Type) [Field F] [NumberField F] (a : F) (m : ℕ)
  (H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a))ˣ)
  (K : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a))ˣ)
  (P : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F a 3 m H K) (A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F a m H K)
  (T : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData F H K A) (hT : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification T P)

include hT in
theorem rational (x : RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition a 3 m) :
    T.complexPhase (fun i => (T.rationalPhase (P.rational.coordinates x) i : ℂ)) =
      RepresentationTheory.Theta.Adelic.BallGeometryData.realTensorComponents A (fun v j =>
        RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal F a (.inl (A.enumerate v)) (x j)) := by
  have h := hT.2.2.2.2.2.2.1
    (fun v j => RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal F a (.inl (A.enumerate v)) (x j))
  have he : (fun i => (T.realPhase (fun v j => A.real v
      ((P.localFrame (.inl (A.enumerate v))).coordinates
        (fun k => RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal F a (.inl (A.enumerate v)) (x k)) j)) i : ℂ)) =
      (fun i => (T.rationalPhase (P.rational.coordinates x) i : ℂ)) := by
    simp only [P.coordinates_compatible, hT.2.2.2.1]
    norm_cast
  rw [he] at h
  exact h

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.ThetaRationalComplexComparison.CM
