import OAI.AlgebraicGeometry.Foundations.Scheme.SmoothDomainDimension
import Mathlib.Basic.Complex.Basic

/-! # Point Differential Rank -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Affine.PointDifferentialRank

noncomputable section

/-! The actual cotangent fiber at a complex point of a smooth affine domain has the native chart dimension. -/

open scoped TensorProduct

variable {A : Type} [CommRing A] [Algebra ℂ A]

abbrev affinePointDifferentialFiber (x : A →ₐ[ℂ] ℂ) :=
  let _ : Algebra A ℂ := x.toRingHom.toAlgebra
  ℂ ⊗[A] KaehlerDifferential ℂ A

theorem affinePointDifferentialFiber_finrank [IsDomain A] [Algebra.Smooth ℂ A] (x : A →ₐ[ℂ] ℂ) :
    Module.finrank ℂ (affinePointDifferentialFiber x) = Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A := by
  let : Algebra A ℂ := x.toRingHom.toAlgebra
  let p : PrimeSpectrum ℂ := ⟨⊥, inferInstance⟩
  have h := Module.rankAtStalk_baseChange (R := A) (M := KaehlerDifferential ℂ A) p
  have hg := Foundations.Scheme.SmoothDomainDimension.Algebraic.kaehler_rankAtStalk_eq_generic (R := ℂ) (S := A) (p.comap (algebraMap A ℂ))
  simpa using h.trans hg

end

end OAI.AlgebraicGeometry.Comparison.Betti.Affine.PointDifferentialRank
