import OAI.Analysis.PDE.Dirichlet.C2HolderImplicit

noncomputable section
open Set Filter Module
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

section General
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Invertibility persists near the smooth base in the Banach topology.
No spatial smoothness of nearby points is involved. -/
theorem isOpen_derivative_invertible {F : X → Y} (hF : ContDiff ℝ 2 F) :
    IsOpen {x | (fderiv ℝ F x).IsInvertible} := by
  exact ContinuousLinearMap.isOpen_setOfPred_isInvertible.preimage
    (hF.fderiv_right (m := 0) (by norm_num)).continuous

theorem eventually_derivative_invertible {F : X → Y} (hF : ContDiff ℝ 2 F)
    {x : X} (hx : (fderiv ℝ F x).IsInvertible) :
    ∀ᶠ y in 𝓝 x, (fderiv ℝ F y).IsInvertible :=
  (isOpen_derivative_invertible hF).eventually_mem hx

theorem inverse_branch_eventually_invertible {F : X → Y} (hF : ContDiff ℝ 2 F)
    {x : X} (hx : (fderiv ℝ F x).IsInvertible) {G : Y → X}
    (hG : ContinuousAt G (F x)) (hGx : G (F x) = x)
    (hr : ∀ᶠ y in 𝓝 (F x), F (G y) = y) :
    ∀ᶠ y in 𝓝 (F x), F (G y) = y ∧ (fderiv ℝ F (G y)).IsInvertible := by
  have ht : Tendsto G (𝓝 (F x)) (𝓝 x) := by
    simpa only [ContinuousAt,hGx] using hG
  exact hr.and (ht.eventually (eventually_derivative_invertible hF hx))

theorem smooth_localInverse_with_invertible_derivative
    {F : X → Y} (hF : ContDiff ℝ ∞ F) (x : X) (L : X ≃L[ℝ] Y)
    (hL : fderiv ℝ F x = L.toContinuousLinearMap) :
    ∃ G : Y → X, ContDiffAt ℝ ∞ G (F x) ∧ G (F x) = x ∧
      (∀ᶠ y in 𝓝 (F x), F (G y) = y ∧ (fderiv ℝ F (G y)).IsInvertible) ∧
      (∀ᶠ z in 𝓝 x, G (F z) = z) := by
  have hd : HasFDerivAt F L.toContinuousLinearMap x := by
    rw [← hL]
    exact (hF.differentiable (by simp) x).hasFDerivAt
  have hs := hF.contDiffAt.hasStrictFDerivAt' hd (by simp)
  let G := hF.contDiffAt.localInverse hd (by simp)
  have hG : ContDiffAt ℝ ∞ G (F x) := hF.contDiffAt.to_localInverse hd (by simp)
  have hGx : G (F x) = x := hF.contDiffAt.localInverse_apply_image hd (by simp)
  have hi : (fderiv ℝ F x).IsInvertible := by
    rw [hL]
    exact ⟨L,rfl⟩
  exact ⟨G,hG,hGx,inverse_branch_eventually_invertible (hF.of_le (by simp))
    hi hG.continuousAt hGx hs.eventually_right_inverse,hs.eventually_left_inverse⟩

end General

variable {m s : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {Ω K : Set (CoordinateSpace m s)} {hΩK : Ω ⊆ K} {α : ℝ}
  {e : CoordinateSpace m s ≃L[ℝ] P × V} {b : Basis ι ℝ P}

local instance invertibleFirstGroup : NormedAddCommGroup (CoordinateSpace m s →L[ℝ] ℝ) := inferInstance
local instance invertibleFirstSpace : NormedSpace ℝ (CoordinateSpace m s →L[ℝ] ℝ) := inferInstance
local instance invertibleSecondGroup : NormedAddCommGroup
    (CoordinateSpace m s →L[ℝ] CoordinateSpace m s →L[ℝ] ℝ) := inferInstance
local instance invertibleSecondSpace : NormedSpace ℝ
    (CoordinateSpace m s →L[ℝ] CoordinateSpace m s →L[ℝ] ℝ) := inferInstance
local instance invertibleHolderGroup : NormedAddCommGroup (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α) := inferInstance
local instance invertibleHolderSpace : NormedSpace ℝ (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α) := inferInstance

omit [Fintype ι] in
/-- The actual periodic Moore derivative is invertible on an open Banach
neighborhood of any invertible base point, including all rough points in
that neighborhood. -/
theorem periodicMooreDirichlet_invertible_neighborhood
    (hΩ : IsOpen Ω) (hKΩ : K ⊆ closure Ω)
    (hΩper : LatticePeriodic e b (fun x ↦ x ∈ Ω))
    (hKper : LatticePeriodic e b (fun x ↦ x ∈ K))
    (hα : 0 ≤ α) (slots : Fin s → Q) (v : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α)
    (hv : LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value v)))
    (u : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b)
    (hinv : (fderiv ℝ
      (periodicMooreDirichletOperator hΩ hKΩ hΩper hKper hα slots v hv) u).IsInvertible) :
    ∃ O : Set (OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b),
      IsOpen O ∧ u ∈ O ∧ ∀ w ∈ O, (fderiv ℝ
        (periodicMooreDirichletOperator hΩ hKΩ hΩper hKper hα slots v hv) w).IsInvertible := by
  let : Fact (IsOpen Ω) := ⟨hΩ⟩
  let F := periodicMooreDirichletOperator hΩ hKΩ hΩper hKper hα slots v hv
  have hF : ContDiff ℝ 2 F :=
    (contDiff_periodicMooreDirichletOperator hΩ hKΩ hΩper hKper hα slots v hv).of_le (by simp)
  exact ⟨{w | (fderiv ℝ F w).IsInvertible},isOpen_derivative_invertible hF,hinv,
    fun _ hw ↦ hw⟩

omit [Fintype ι] in
/-- The existing local inverse can be restricted so that its entire rough
solution branch has invertible derivative. This is the input for the
geometric parameter IFT at each of those rough solutions. -/
theorem periodicMooreDirichlet_localInverse_invertible
    (hΩ : IsOpen Ω) (hKΩ : K ⊆ closure Ω)
    (hΩper : LatticePeriodic e b (fun x ↦ x ∈ Ω))
    (hKper : LatticePeriodic e b (fun x ↦ x ∈ K))
    (hα : 0 ≤ α) (slots : Fin s → Q) (v : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α)
    (hv : LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value v)))
    (u : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b)
    (L : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b ≃L[ℝ]
      OAI.Analysis.Normed.Function.Holder.LatticeHolderSpace (K := K) (α := α) e b)
    (hL : fderiv ℝ (periodicMooreDirichletOperator hΩ hKΩ hΩper hKper hα slots v hv) u =
      L.toContinuousLinearMap) :
    let F := periodicMooreDirichletOperator hΩ hKΩ hΩper hKper hα slots v hv
    ∃ G : OAI.Analysis.Normed.Function.Holder.LatticeHolderSpace (K := K) (α := α) e b →
      OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b,
      ContDiffAt ℝ ∞ G (F u) ∧ G (F u) = u ∧
      (∀ᶠ y in 𝓝 (F u), F (G y) = y ∧ (fderiv ℝ F (G y)).IsInvertible) ∧
      (∀ᶠ z in 𝓝 u, G (F z) = z) := by
  let : Fact (IsOpen Ω) := ⟨hΩ⟩
  dsimp only
  exact smooth_localInverse_with_invertible_derivative
    (contDiff_periodicMooreDirichletOperator hΩ hKΩ hΩper hKper hα slots v hv) u L hL

end OAI.Analysis.PDE.Dirichlet
