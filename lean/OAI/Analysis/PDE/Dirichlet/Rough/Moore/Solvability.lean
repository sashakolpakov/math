import OAI.Analysis.PDE.Dirichlet.Rough.Moore

open Set Module
open scoped ContDiff Matrix.Norms.Elementwise ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.LinearAlgebra.Moore

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

def MooreDirichletSolvable
    (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {Ω D : Set (CoordinateSpace n 4)} (hΩD : Ω ⊆ D) (α : ℝ)
    (A : D → Matrix (Fin n) (Fin n) Q) : Prop :=
  ∀ f : OAI.Analysis.Normed.Function.Holder.LatticeHolderSpace (K := D) (α := α) e lat,
    ∃ w : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α, w ∈ OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet e lat ∧
      ∀ x, OAI.LinearAlgebra.Moore.mooreDifferential n (A x)
        (OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩD α OAI.Analysis.Calculus.Quaternion.fourSlots w) x) = OAI.Analysis.Normed.Function.Holder.HolderMap.value f.val x

omit [Fintype ι] in
theorem MooreDirichletSolvable.congr
    {e : CoordinateSpace n 4 ≃L[ℝ] P × V} {lat : Basis ι ℝ P}
    {Ω D : Set (CoordinateSpace n 4)} {hΩD : Ω ⊆ D} {α : ℝ}
    {A B : D → Matrix (Fin n) (Fin n) Q}
    (h : MooreDirichletSolvable e lat hΩD α A) (hAB : ∀ x, B x = A x) :
    MooreDirichletSolvable e lat hΩD α B := by
  have he : B = A := funext hAB
  rwa [he]

omit [Fintype ι] in
theorem mooreDirichletSolvable_of_bounded
    (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {Ω D : Set (CoordinateSpace n 4)} {hΩD : Ω ⊆ D} {α : ℝ}
    (A : D → Matrix (Fin n) (Fin n) Q)
    (h : ∃ C : ℝ, 0 < C ∧
      ∀ f : OAI.Analysis.Normed.Function.Holder.LatticeHolderSpace (K := D) (α := α) e lat,
      ∃ w : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α, ‖w‖ ≤ C * ‖f‖ ∧
        w ∈ OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet e lat ∧
        ∀ x, OAI.LinearAlgebra.Moore.mooreDifferential n (A x)
          (OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩD α OAI.Analysis.Calculus.Quaternion.fourSlots w) x) = OAI.Analysis.Normed.Function.Holder.HolderMap.value f.val x) :
    MooreDirichletSolvable e lat hΩD α A := by
  obtain ⟨C, hC, h⟩ := h
  intro f
  obtain ⟨w, hwC, hw, hwe⟩ := h f
  exact ⟨w, hw, hwe⟩

variable [FiniteDimensional ℝ P] [FiniteDimensional ℝ V] [Nontrivial V]

omit [FiniteDimensional ℝ P] in
theorem mooreDirichletSolvable_of_uniform_schauder
    (hn : 1 ≤ n) (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {K : Set V} (hK : IsCompact K)
    {r : CoordinateSpace n 4 → ℝ} (hr : ContDiff ℝ ∞ r) (hrp : LatticePeriodic e lat r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hrpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef)
    [Nonempty {x | r x ≤ 0}]
    {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hschauder : UniformPeriodicMooreSchauderEstimate e lat hΩD α)
    (ψ : CoordinateSpace n 4 → ℝ) (hψ : ContDiff ℝ 3 ψ) (hψp : LatticePeriodic e lat ψ)
    (hψpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef) :
    MooreDirichletSolvable e lat hΩD α (fun x ↦ quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) :=
  mooreDirichletSolvable_of_bounded e lat _
    (exists_C3_moore_dirichlet_solution_of_uniform_schauder
      hn e lat hK hr hrp hbounded hreg hrpos hα hα1 hschauder ψ hψ hψp hψpos)

end OAI.Analysis.PDE.Dirichlet
