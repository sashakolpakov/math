import OAI.Analysis.PDE.Elliptic.Boundary.Fourth.DoubleHolder
import OAI.Analysis.Calculus.SmoothExtension.DirichletInteriorPeriodicFields

noncomputable section
open Set Filter Metric Module
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.PDE.Elliptic OAI.Analysis.Calculus.SmoothExtension

variable {E P V ι Z : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

/-- The uniform consequence of solving the twice-tangential linearized
Dirichlet equation. Its conclusion is about actual derivative fields. -/
def UniformPeriodicDoubleFieldBounds (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    (r : E → ℝ) (α : ℝ) (u : Z → E → ℝ) : Prop :=
  ∀ T W : E → E, ContDiff ℝ ∞ T → ContDiff ℝ ∞ W →
    LatticePeriodic e lat T → LatticePeriodic e lat W →
    (∀ x, r x = 0 → fderiv ℝ r x (T x) = 0) →
    (∀ x, r x = 0 → fderiv ℝ r x (W x) = 0) →
    ∃ M > 0, ∀ z, OAI.Analysis.PDE.Elliptic.HasDoubleFieldHolderBound {x | r x ≤ 0} α (u z) T W M

/-- The same global tangential inverse estimates control all fourth
derivatives in the interior, by extending locally constant fields. -/
theorem UniformPeriodicDoubleFieldBounds.interior_fourth_bound
    {e : E ≃L[ℝ] P × V} {lat : Basis ι ℝ P} {r : E → ℝ} {α : ℝ}
    {u : Z → E → ℝ} (h : UniformPeriodicDoubleFieldBounds e lat r α u)
    (hr : Continuous r) (hrp : LatticePeriodic e lat r)
    (hα : 0 ≤ α) (hu : ∀ z, ContDiff ℝ 4 (u z)) {a : E} (ha : r a < 0) :
    ∃ ρ > 0, ∃ C > 0, ∀ z,
      OAI.Analysis.PDE.Elliptic.HasFourthHolderBound (closedBall a ρ ∩ {x | r x ≤ 0}) α (u z) C := by
  classical
  let b := stdOrthonormalBasis ℝ E
  obtain ⟨ρ,hρ,T,hball,hT,hTp,hTtan,hTg⟩ :=
    OAI.Analysis.Calculus.SmoothExtension.exists_interior_periodic_constant_fields e lat hr hrp ha (fun i => b i)
  have hb (p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) :=
    h (T p.1) (T p.2) (hT p.1) (hT p.2) (hTp p.1) (hTp p.2) (hTtan p.1) (hTtan p.2)
  choose M hM hMb using hb
  let N := (∑ p, M p)+1
  have hsum : 0 ≤ ∑ p, M p := Finset.sum_nonneg (fun p _ => (hM p).le)
  have hN : 0 ≤ N := by dsimp [N]; linarith
  have hMN (p) : M p ≤ N := by
    have hle : M p ≤ ∑ q, M q :=
      Finset.single_le_sum (fun q _ => (hM q).le) (Finset.mem_univ p)
    dsimp [N]
    linarith
  let C := (Module.finrank ℝ E : ℝ)^4*N+1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨ρ,hρ,C,hC,?_⟩
  intro z
  have hlocal : OAI.Analysis.PDE.Elliptic.HasFourthHolderBound (closedBall a ρ ∩ {x | r x ≤ 0}) α (u z)
      ((Module.finrank ℝ E : ℝ)^4*N) := by
    suffices H : OAI.Analysis.PDE.Elliptic.HasFourthHolderBound (closedBall a ρ ∩ {x | r x ≤ 0}) α (u z)
        ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ)^4*N) by
      simpa only [Fintype.card_fin] using H
    apply OAI.Analysis.PDE.Elliptic.fourth_holder_of_constant_field_germs b
      (K := {x | r x ≤ 0}) (S := closedBall a ρ ∩ {x | r x ≤ 0})
      (fun x hx => hx.2) hα hN (u z) (hu z) T
    · intro i x
      exact hTg i x x.property.1
    · intro i j
      obtain ⟨B,hB,hBn⟩ := hMb (i,j) z
      exact ⟨B,hB,hBn.trans (hMN (i,j))⟩
  exact hlocal.mono (by dsimp [C]; linarith)

end OAI.Analysis.PDE.Dirichlet
