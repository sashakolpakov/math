import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.CoefficientPadic
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LatticeGenerators
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SplitLatticeProduct

/-! # Split Vector Evaluation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SplitVectorEvaluation.TestTransport

noncomputable section

/-! Linear evaluation of all finite coefficient vectors at a specified
family of split embeddings, retaining rational vectors and their basis. -/

open scoped Classical

variable (E : Type) [Field E] [NumberField E] {q : ℕ} [Fact q.Prime]
  {S I : Type*} (σ : S → E →+* Padic q)

def finiteSplitEvaluation : (I → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) →ₗ[ℚ] (S → I → Padic q) :=
  LinearMap.pi (fun v => LinearMap.pi (fun i =>
    (Finite.CoefficientPadic.TestTransport.finiteCoefficientPadic E (σ v)).toLinearMap.comp (LinearMap.proj i)))

def rationalSplitEmbedding : (I → E) →ₗ[ℚ] (S → I → Padic q) :=
  LinearMap.pi (fun v => LinearMap.pi (fun i =>
    (σ v).toRatAlgHom.toLinearMap.comp (LinearMap.proj i)))

theorem finiteSplitEvaluation_rational (x : I → E) :
    finiteSplitEvaluation E σ (fun i => AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E (x i)) =
      rationalSplitEmbedding E σ x := by
  funext v i
  exact Finite.CoefficientPadic.TestTransport.finiteCoefficientPadic_rational E (σ v) (x i)

theorem splitLatticeImage_span_basis {J : Type*} [Fintype J]
    (L : Submodule ℤ (I → E)) (b : Module.Basis J ℤ L) :
    Submodule.span (PadicInt q) (Set.range (fun j => rationalSplitEmbedding E σ (b j).val)) =
      SplitLatticeProduct.TestTransport.splitLatticeImage (R := PadicInt q) σ L :=
  LatticeGenerators.TestTransport.span_image_integral_basis L b (rationalSplitEmbedding E σ).toAddMonoidHom

theorem span_basis_preserves_iff {R V J : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] (M : Submodule R V) (b : J → V)
    (hb : Submodule.span R (Set.range b) = M) (f : V →ₗ[R] V) :
    (∀ j, f (b j) ∈ M) ↔ ∀ x ∈ M, f x ∈ M := by
  constructor
  · intro h
    have hs : Submodule.span R (Set.range b) ≤ M.comap f :=
      Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact h j)
    exact le_trans (le_of_eq hb.symm) hs
  · intro h j
    exact h _ (hb ▸ Submodule.subset_span (Set.mem_range_self j))

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SplitVectorEvaluation.TestTransport
