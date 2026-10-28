import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeEq
import Mathlib.Analysis.Analytic.Polynomial

/-! # Polynomial Separation Finite -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.PolynomialSeparationFinite.Constructions.PolynomialSeparation

noncomputable section

/-! # RiemannProjectivity: polynomial separation gives finite homogeneous cone equations -/

open Set Filter
open scoped _root_.Topology

theorem finite_equations {d : ℕ} {S : Set (Fin d → ℂ)}
    (hsep : ∀ v, v ∉ S → ∃ p : MvPolynomial (Fin d) ℂ,
      (∀ w ∈ S, MvPolynomial.eval w p = 0) ∧ MvPolynomial.eval v p ≠ 0) :
    ∃ Q : Finset (MvPolynomial (Fin d) ℂ), S = {z | ∀ q ∈ Q, MvPolynomial.eval z q = 0} := by
  classical
  let I : Set (MvPolynomial (Fin d) ℂ) := {p | ∀ w ∈ S, MvPolynomial.eval w p = 0}
  obtain ⟨Q, hQ, hspan⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset (R := MvPolynomial (Fin d) ℂ) I).mp
      (IsNoetherian.noetherian _)
  change Ideal.span I = Ideal.span (Q : Set (MvPolynomial (Fin d) ℂ)) at hspan
  refine ⟨Q, Set.ext (fun z => ⟨fun hz q hq => hQ hq z hz, ?_⟩)⟩
  intro hz
  by_contra hzS
  obtain ⟨p, hp, hpz⟩ := hsep z hzS
  have hker : Ideal.span (Q : Set (MvPolynomial (Fin d) ℂ)) ≤
      RingHom.ker (MvPolynomial.eval z) := Ideal.span_le.mpr (fun q hq => hz q hq)
  apply hpz
  apply hker
  rw [← hspan]
  exact Ideal.subset_span hp

theorem homogeneous_equations {d : ℕ} {S : Set (Fin d → ℂ)}
    (hcone : ∀ (c : ℂ) ⦃v⦄, v ∈ S → c • v ∈ S)
    (hsep : ∀ v, v ∉ S → ∃ p : MvPolynomial (Fin d) ℂ,
      (∀ w ∈ S, MvPolynomial.eval w p = 0) ∧ MvPolynomial.eval v p ≠ 0) :
    ∃ Q : Finset (MvPolynomial (Fin d) ℂ),
      (∀ q ∈ Q, ∃ n, q.IsHomogeneous n) ∧ S = {z | ∀ q ∈ Q, MvPolynomial.eval z q = 0} := by
  classical
  obtain ⟨P, hP⟩ := finite_equations hsep
  let e : Fin (Fintype.card P) ≃ P := (Fintype.equivFin P).symm
  let f : Fin (Fintype.card P) → (Fin d → ℂ) → ℂ := fun i z => MvPolynomial.eval z (e i).val
  have hf (i : Fin (Fintype.card P)) : AnalyticAt ℂ (f i) 0 :=
    AnalyticOnNhd.eval_mvPolynomial (e i).val 0 (mem_univ _)
  apply AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeEq.Constructions.Cone.finite_equations_from_analytic_vertex hcone f hf
  apply Filter.Eventually.of_forall
  intro z
  rw [hP]
  change (∀ q ∈ P, MvPolynomial.eval z q = 0) ↔ ∀ i, MvPolynomial.eval z (e i).val = 0
  constructor
  · intro hz i
    exact hz _ (e i).property
  · intro hz q hq
    obtain ⟨i, hi⟩ := e.surjective ⟨q, hq⟩
    simpa only [hi] using hz i

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.PolynomialSeparationFinite.Constructions.PolynomialSeparation
