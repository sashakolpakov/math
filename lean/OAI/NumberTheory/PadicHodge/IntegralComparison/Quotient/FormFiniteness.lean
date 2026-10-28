import OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.DifferentialBasis

/-! # Form Finiteness -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.FormFiniteness

noncomputable section

/-! Finite free forms on the actual quotient ring with its original structural algebra action. -/

universe u

variable (R A σ : Type u) [CommRing R] [CommRing A] [Algebra R A] [LinearOrder σ]
  (I : Ideal R) (J : Ideal A) (hJ : J = I.map (algebraMap R A))
  (x : σ → A) (b : Module.Basis σ A (KaehlerDifferential R A))
  (hb : ∀ i, b i = KaehlerDifferential.D R A (x i))

include hJ x b hb in
theorem finite [Finite σ] (n : ℕ) :
    Module.Finite (A ⧸ J) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R (A ⧸ J) n) := by
  subst J
  exact DifferentialBasis.finite R A σ I x b hb n

include hJ x b hb in
theorem free (n : ℕ) : Module.Free (A ⧸ J) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R (A ⧸ J) n) := by
  subst J
  exact DifferentialBasis.free R A σ I x b hb n

include hJ x b hb in
theorem structural_finite [Finite σ] (n : ℕ) :
    letI : Algebra R (A ⧸ J) := ((Ideal.Quotient.mk J).comp (algebraMap R A)).toAlgebra
    Module.Finite (A ⧸ J) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R (A ⧸ J) n) := by
  have he : ((Ideal.Quotient.mk J).comp (algebraMap R A)).toAlgebra =
      (inferInstance : Algebra R (A ⧸ J)) := Algebra.algebra_ext _ _ (fun _ => rfl)
  rw [he]
  exact finite R A σ I J hJ x b hb n

include hJ x b hb in
theorem structural_free (n : ℕ) :
    letI : Algebra R (A ⧸ J) := ((Ideal.Quotient.mk J).comp (algebraMap R A)).toAlgebra
    Module.Free (A ⧸ J) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R (A ⧸ J) n) := by
  have he : ((Ideal.Quotient.mk J).comp (algebraMap R A)).toAlgebra =
      (inferInstance : Algebra R (A ⧸ J)) := Algebra.algebra_ext _ _ (fun _ => rfl)
  rw [he]
  exact free R A σ I J hJ x b hb n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.FormFiniteness
