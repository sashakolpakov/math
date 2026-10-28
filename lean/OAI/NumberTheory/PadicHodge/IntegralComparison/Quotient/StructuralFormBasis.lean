import OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.DifferentialBasis

/-! # Structural Form Basis -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.StructuralFormBasis

noncomputable section

/-! Coordinate form bases with the exact structural algebra action of the original frame. -/

universe u

variable (R A σ : Type u) [CommRing R] [CommRing A] [Algebra R A] [LinearOrder σ]
  (I : Ideal R) (J : Ideal A) (hJ : J = I.map (algebraMap R A))
  (x : σ → A) (b : Module.Basis σ A (KaehlerDifferential R A))
  (hb : ∀ i, b i = KaehlerDifferential.D R A (x i))

include hJ hb in
theorem exists_basis (n : ℕ) :
    letI : Algebra R (A ⧸ J) := ((Ideal.Quotient.mk J).comp (algebraMap R A)).toAlgebra
    ∃ c : Module.Basis (Set.powersetCard σ n) (A ⧸ J) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R (A ⧸ J) n),
      ∀ s, c s = AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R (A ⧸ J) 1
        (fun j => Ideal.Quotient.mk J (x (Set.powersetCard.ofFinEmbEquiv.symm s j))) := by
  have he : ((Ideal.Quotient.mk J).comp (algebraMap R A)).toAlgebra =
      (inferInstance : Algebra R (A ⧸ J)) := Algebra.algebra_ext _ _ (fun _ => rfl)
  rw [he]
  subst J
  exact ⟨DifferentialBasis.basis R A σ I x b hb n,
    DifferentialBasis.basis_apply R A σ I x b hb n⟩

def basis (n : ℕ) :
    letI : Algebra R (A ⧸ J) := ((Ideal.Quotient.mk J).comp (algebraMap R A)).toAlgebra
    Module.Basis (Set.powersetCard σ n) (A ⧸ J) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R (A ⧸ J) n) :=
  (exists_basis R A σ I J hJ x b hb n).choose

theorem basis_apply (n : ℕ) (s : Set.powersetCard σ n) :
    letI : Algebra R (A ⧸ J) := ((Ideal.Quotient.mk J).comp (algebraMap R A)).toAlgebra
    basis R A σ I J hJ x b hb n s = AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R (A ⧸ J) 1
      (fun j => Ideal.Quotient.mk J (x (Set.powersetCard.ofFinEmbEquiv.symm s j))) :=
  (exists_basis R A σ I J hJ x b hb n).choose_spec s

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.StructuralFormBasis
