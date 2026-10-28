import OAI.AlgebraicGeometry.Comparison.Betti.Affine.ChartCotangentRealization

/-! # Tangent Derivation -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Affine.TangentDerivation

noncomputable section

/-! A native chart tangent vector differentiates actual regular functions at the given point. -/

variable {A : Type} [CommRing A] [Algebra ℂ A] {n : ℕ}

def affineChartTangentDerivation
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin n → ℂ))
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A n) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (hx : x ∈ e.source)
    (v : Fin n → ℂ) :
    let _ : Algebra A ℂ := x.toRingHom.toAlgebra
    Derivation ℂ A ℂ := by
  let : Algebra A ℂ := x.toRingHom.toAlgebra
  let : Module A (Module.Dual ℂ (Fin n → ℂ)) :=
    Module.compHom (Module.Dual ℂ (Fin n → ℂ)) x.toRingHom
  let D : Derivation ℂ A (Module.Dual ℂ (Fin n → ℂ)) :=
    ChartCotangentRealization.affineChartRegularDerivation e he x hx
  exact
    { toFun := fun a => D a v
      map_add' := fun a b => by simp only [map_add, LinearMap.add_apply]
      map_smul' := fun c a => congrArg (fun L : Module.Dual ℂ (Fin n → ℂ) => L v)
        (D.toLinearMap.map_smul c a)
      map_one_eq_zero' := by
        change D 1 v = 0
        rw [D.map_one_eq_zero]
        rfl
      leibniz' := fun a b => by
        change D (a * b) v = x a * D b v + x b * D a v
        rw [D.leibniz]
        rfl }

theorem affineChartTangentDerivation_apply
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin n → ℂ))
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A n) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (hx : x ∈ e.source)
    (v : Fin n → ℂ) (a : A) :
    affineChartTangentDerivation e he x hx v a = ChartCotangentRealization.affineChartRegularDifferential e x a v := rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.Affine.TangentDerivation
