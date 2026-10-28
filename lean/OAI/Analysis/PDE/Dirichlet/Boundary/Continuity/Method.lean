import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Sequences
import OAI.Analysis.PDE.Dirichlet.InitialSolution

noncomputable section
open Set Filter Module
open scoped Topology

namespace OAI.Analysis.PDE.Dirichlet

/-- The topological part of the continuity method, with sequential closedness
and relative openness stated on the actual parameter interval. -/
theorem continuity_method_interval (P : ℝ → Prop) (hzero : P 0)
    (hclosed : ∀ (s : ℕ → ℝ) (t : ℝ), (∀ k, s k ∈ Icc (0 : ℝ) 1) →
      (∀ k, P (s k)) → t ∈ Icc (0 : ℝ) 1 → Tendsto s atTop (𝓝 t) → P t)
    (hopen : ∀ t ∈ Icc (0 : ℝ) 1, P t →
      ∀ᶠ y in 𝓝 t, y ∈ Icc (0 : ℝ) 1 → P y) :
    ∀ t ∈ Icc (0 : ℝ) 1, P t := by
  let S : Set (Icc (0 : ℝ) 1) := {t | P t}
  have hSclosed : IsClosed S := IsSeqClosed.isClosed (by
    intro s t hs ht
    exact hclosed (fun k => (s k).val) t (fun k => (s k).property) hs t.property
      ((continuous_subtype_val.tendsto t).comp ht))
  have hSopen : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    filter_upwards [(continuous_subtype_val.tendsto t).eventually
      (hopen t t.property ht)] with y hy
    exact hy y.property
  have hfull : S = univ := (show IsClopen S from ⟨hSclosed,hSopen⟩).eq_univ
    ⟨⟨0,by constructor <;> norm_num⟩,hzero⟩
  intro t ht
  have hm : (⟨t,ht⟩ : Icc (0 : ℝ) 1) ∈ S := hfull ▸ mem_univ _
  exact hm

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

def SmoothPathSolvable
    (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    (r B₀ F₀ F₁ : CoordinateSpace n 4 → ℝ) (t : ℝ) : Prop :=
  ∃ s : SmoothPathSolution e lat r B₀ F₀ F₁, s.t = t

theorem SmoothPathSolvable.all_parameters
    (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {r B₀ F₀ F₁ : CoordinateSpace n 4 → ℝ}
    (hzero : SmoothPathSolvable e lat r B₀ F₀ F₁ 0)
    (hclosed : ∀ (s : ℕ → SmoothPathSolution e lat r B₀ F₀ F₁) (t : ℝ),
      t ∈ Icc (0 : ℝ) 1 → Tendsto (fun k => (s k).t) atTop (𝓝 t) →
      SmoothPathSolvable e lat r B₀ F₀ F₁ t)
    (hopen : ∀ s : SmoothPathSolution e lat r B₀ F₀ F₁,
      ∀ᶠ y in 𝓝 s.t, y ∈ Icc (0 : ℝ) 1 → SmoothPathSolvable e lat r B₀ F₀ F₁ y) :
    ∀ t ∈ Icc (0 : ℝ) 1, SmoothPathSolvable e lat r B₀ F₀ F₁ t := by
  apply continuity_method_interval _ hzero
  · intro a t _ ha ht hat
    choose s hs using ha
    apply hclosed s t ht
    simpa only [hs] using hat
  · intro t _ ht
    obtain ⟨s,rfl⟩ := ht
    exact hopen s

open scoped ComplexOrder Matrix.Norms.Elementwise
open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

theorem SmoothPathSolvable.of_classical_potential
    (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {r B₀ F₀ F₁ : CoordinateSpace n 4 → ℝ} {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1)
    (hB₀ : ContDiff ℝ 4 B₀) (hB₀p : LatticePeriodic e lat B₀)
    (ψ : CoordinateSpace n 4 → ℝ) (hψ : ContDiff ℝ 4 ψ)
    (hψp : LatticePeriodic e lat ψ) (hψbd : ∀ x, r x = 0 → ψ x = B₀ x)
    (hψpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef)
    (hψeq : ∀ x, r x ≤ 0 → OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) =
      densityPath F₀ F₁ t x) :
    SmoothPathSolvable e lat r B₀ F₀ F₁ t := by
  have hfun : (fun x => B₀ x+(ψ x-B₀ x)) = ψ := by funext x; ring
  refine ⟨{
    t := t
    parameter := ht
    u := fun x => ψ x-B₀ x
    smooth := hψ.sub hB₀
    periodic := by
      intro x l
      change ψ (e.symm ((e x).1+(l:P),(e x).2)) -
        B₀ (e.symm ((e x).1+(l:P),(e x).2)) = ψ x-B₀ x
      rw [hψp x l,hB₀p x l]
    zero := fun x hx => sub_eq_zero.mpr (hψbd x hx)
    positive := ?_
    equation := ?_
  },rfl⟩
  · intro x hx
    rw [hfun]
    exact hψpos x hx.le
  · intro x hx
    rw [hfun]
    exact hψeq x hx.le

end OAI.Analysis.PDE.Dirichlet
