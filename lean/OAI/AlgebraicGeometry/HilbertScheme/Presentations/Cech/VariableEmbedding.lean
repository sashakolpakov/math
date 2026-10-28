import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.Signs
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.LaurentMonomials
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.KillVariables
import Mathlib.Data.Finset.Image

/-! # Variable Embedding -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.VariableEmbedding.ProjectiveCech

noncomputable section

/-! Ordered embeddings of variable sets preserve Čech signs and chart denominator monomials. -/

universe u v w

variable {σ : Type u} {τ : Type v}
variable (R : Type w) [CommRing R]

theorem inversionExponent_map (e : σ ↪ τ) (s : Finset σ) :
    LaurentExponents.ProjectiveCech.inversionExponent (s.map e) = (LaurentExponents.ProjectiveCech.inversionExponent s).mapDomain e := by
  classical
  simp only [LaurentExponents.ProjectiveCech.inversionExponent, Finset.sum_map, Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_single]

theorem inversionMonomial_map (e : σ ↪ τ) (s : Finset σ) :
    LaurentMonomials.ProjectiveCech.inversionMonomial R (s.map e) = MvPolynomial.rename e (LaurentMonomials.ProjectiveCech.inversionMonomial R s) := by
  rw [LaurentMonomials.ProjectiveCech.inversionMonomial, LaurentMonomials.ProjectiveCech.inversionMonomial, MvPolynomial.rename_monomial, inversionExponent_map]

theorem killVariables_inversionMonomial_map (e : σ ↪ τ) (s : Finset σ) :
    MvPolynomial.killCompl (R := R) e.injective (LaurentMonomials.ProjectiveCech.inversionMonomial R (s.map e)) =
      LaurentMonomials.ProjectiveCech.inversionMonomial R s := by
  rw [inversionMonomial_map, MvPolynomial.killCompl_rename_app]

theorem killVariables_inversionMonomial_zero (e : σ ↪ τ) (s : Finset τ)
    (j : τ) (hj : j ∈ s) (hje : j ∉ Set.range e) :
    MvPolynomial.killCompl (R := R) e.injective (LaurentMonomials.ProjectiveCech.inversionMonomial R s) = 0 := by
  classical
  apply MvPolynomial.killCompl_monomial_eq_zero_of_notMem_range e.injective 1 _ hje
  rw [Finsupp.mem_support_iff, LaurentExponents.ProjectiveCech.inversionExponent_apply, ite_eq_left hj]
  exact one_ne_zero

variable [LinearOrder σ] [LinearOrder τ]

theorem alternatingSign_map (e : σ ↪o τ) (s : Finset σ) (i : σ) :
    Signs.ProjectiveCech.alternatingSign R (s.map e.toEmbedding) (e i) = Signs.ProjectiveCech.alternatingSign R s i := by
  unfold Signs.ProjectiveCech.alternatingSign
  rw [Finset.filter_map]
  have he : s.filter (fun j : σ => e j < e i) = s.filter (fun j => j < i) := by
    apply Finset.filter_congr
    intro j _
    exact e.lt_iff_lt
  change (-1 : R) ^ ((s.filter (fun j => e j < e i)).map e.toEmbedding).card = _
  rw [he, Finset.card_map]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.VariableEmbedding.ProjectiveCech
