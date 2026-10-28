import OAI.RepresentationTheory.Theta.Adelic.DataTheta

/-! # One Tensor Complex -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OneTensorComplex.Quadratic

noncomputable section

/-! The complete AdelicTheta coordinate clauses identify the complexification of
every rational tensor with its actual local CM tensor components. -/

open scoped Classical _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
  {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  {K : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  {A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d m H K}
  (B : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData F H K A) (P : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K)

theorem complexPhase_rational_tensor (hCoord : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification B P)
    (x : RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition d 3 m) :
    B.complexPhase (fun i => (B.rationalPhase (P.rational.coordinates x) i : ℂ)) =
      RepresentationTheory.Theta.Adelic.BallGeometryData.realTensorComponents A (fun v j =>
        RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal F d (.inl (A.enumerate v)) (x j)) := by
  have h := hCoord.2.2.2.2.2.2.1
    (fun v j => RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal F d (.inl (A.enumerate v)) (x j))
  have he :
      (fun v j => A.real v ((P.localFrame (.inl (A.enumerate v))).coordinates
        (fun j => RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal F d (.inl (A.enumerate v)) (x j)) j)) =
      (fun v j => A.real v (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v))
        (P.rational.coordinates x j))) := by
    funext v j
    rw [P.coordinates_compatible]
  rw [he] at h
  have hc : (fun i => (B.realPhase
      (fun v j => A.real v (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v))
        (P.rational.coordinates x j))) i : ℂ)) =
      (fun i => (B.rationalPhase (P.rational.coordinates x) i : ℂ)) := by
    funext i
    rw [hCoord.2.2.2.1]
    norm_cast
  rw [hc] at h
  exact h

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OneTensorComplex.Quadratic
