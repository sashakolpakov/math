import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.FreeModule.Basic

/-! # Monic Polynomial Quotient Free -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.MonicPolynomialQuotientFree

noncomputable section

/-! A leading-term cover with unit leading coefficients gives a free
polynomial quotient over an arbitrary coefficient ring. -/

open _root_.MvPolynomial _root_.Module

universe u v w
variable {R : Type u} [CommRing R] {σ : Type v}

theorem monic_leading_cover_quotient_free (m : MonomialOrder σ)
    (I : Ideal (MvPolynomial σ R)) {ι : Type w} (b : ι → MvPolynomial σ R)
    (hb : ∀ i, b i ∈ I) (hu : ∀ i, IsUnit (m.leadingCoeff (b i)))
    (hc : ∀ f ∈ I, f ≠ 0 → ∃ i, m.degree (b i) ≤ m.degree f) :
    Module.Free R (MvPolynomial σ R ⧸ I) := by
  let S : Submodule R (MvPolynomial σ R) :=
    restrictSupport R {a | ∀ i, ¬ m.degree (b i) ≤ a}
  have hd : Disjoint (I.restrictScalars R) S := by
    apply Submodule.disjoint_def.mpr
    intro f hf hs
    by_contra hf0
    obtain ⟨i, hi⟩ := hc f hf hf0
    exact hs (m.degree_mem_support hf0) i hi
  have hsup : I.restrictScalars R ⊔ S = ⊤ := by
    apply top_unique
    intro f _
    obtain ⟨g, r, hfr, _, hr⟩ := m.div hu f
    have hg : Finsupp.linearCombination (MvPolynomial σ R) b g ∈ I := by
      rw [Finsupp.linearCombination_apply, Finsupp.sum]
      exact I.sum_mem fun i _ => I.mul_mem_left (g i) (hb i)
    exact Submodule.mem_sup.mpr ⟨_, hg, r, hr, hfr.symm⟩
  have hcompl : IsCompl (I.restrictScalars R) S := ⟨hd, codisjoint_iff.mpr hsup⟩
  let e := Submodule.quotientEquivOfIsCompl (I.restrictScalars R) S hcompl
  let : Module.Free R S := Module.Free.of_basis (basisRestrictSupport R _)
  exact Module.Free.of_equiv e.symm

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.MonicPolynomialQuotientFree
