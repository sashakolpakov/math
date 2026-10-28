import OAI.Analysis.PDE.Dirichlet.Fourth.PathEquation
import OAI.Analysis.PDE.Dirichlet.Boundary.UniformClassical

noncomputable section
open Set Module
open scoped ContDiff
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Schauder OAI.Analysis.PDE.Elliptic

theorem exists_norm_bound_mono {X : Type*} [Norm X] {P : X → Prop}
    {a b : ℝ} (h : ∃ x : X, ‖x‖ ≤ a ∧ P x) (hab : a ≤ b) :
    ∃ x : X, ‖x‖ ≤ b ∧ P x := by
  obtain ⟨x,hx,hP⟩ := h
  exact ⟨x,hx.trans hab,hP⟩

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
local notation "E" => CoordinateSpace (n+1) 4
attribute [local instance] uniformClassicalFirstGroup uniformClassicalFirstSpace
  uniformClassicalSecondGroup uniformClassicalSecondSpace

theorem UniformPathClassicalEstimate.second_tangent
    {e : E ≃L[ℝ] P × V} {lat : Basis ι ℝ P}
    {r B₀ F₀ F₁ : E → ℝ} {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    {d : OAI.Analysis.PDE.Schauder.InteriorThirdPathData e lat r B₀ F₀ F₁ hΩK} {C : ℝ}
    (hsolve : UniformPathClassicalEstimate e lat d C)
    (s : SmoothPathSolution e lat r B₀ F₀ F₁)
    (hr : ContDiff ℝ 1 r) (hreg : ∀ x, r x=0 → fderiv ℝ r x ≠ 0)
    (hB₀ : ContDiff ℝ 4 B₀) (hF₀ : ContDiff ℝ 2 F₀) (hF₁ : ContDiff ℝ 2 F₁)
    (T S : E → E) (hT : ContDiff ℝ 3 T) (hS : ContDiff ℝ 2 S)
    (hTp : LatticePeriodic e lat T) (hSp : LatticePeriodic e lat S)
    (hTtan : ∀ x, r x=0 → fderiv ℝ r x (T x)=0)
    (hStan : ∀ x, r x=0 → fderiv ℝ r x (S x)=0)
    (F : OAI.Analysis.Normed.Function.Holder.LatticeHolderSpace (K := {x | r x ≤ 0}) (α := d.exponent/2) e lat)
    (hF : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value F.val x = mooreSecondBackgroundForcing
      (fun y => B₀ y+s.u y) B₀ (densityPath F₀ F₁ s.t) T S x) :
    ∃ U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK (d.exponent/2),
      ‖U‖ ≤ C*‖F‖ ∧ U ∈ OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet e lat ∧
      (∀ x : {x | r x ≤ 0}, OAI.Analysis.PDE.Elliptic.fieldDerivative (OAI.Analysis.PDE.Elliptic.fieldDerivative s.u T) S x = OAI.Analysis.Normed.Function.Holder.C2Holder.value U x) ∧
      (∀ x : {x | r x ≤ 0},
        fderiv ℝ (OAI.Analysis.PDE.Elliptic.fieldDerivative (OAI.Analysis.PDE.Elliptic.fieldDerivative s.u T) S) x = OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U x) ∧
      (∀ x : {x | r x ≤ 0},
        fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Elliptic.fieldDerivative (OAI.Analysis.PDE.Elliptic.fieldDerivative s.u T) S)) x =
          OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U x) := by
  obtain ⟨hw,hwp,hwzero,heq⟩ := s.second_tangent_classical_equation
    hr hreg hB₀ hF₀ hF₁ T S hT hS hTp hSp hTtan hStan
  exact hsolve s F (OAI.Analysis.PDE.Elliptic.fieldDerivative (OAI.Analysis.PDE.Elliptic.fieldDerivative s.u T) S)
    hw hwp hwzero (fun x hx => (heq x hx).trans (hF ⟨x,hΩK hx⟩).symm)

theorem UniformPathClassicalEstimate.uniform_second_tangent
    {e : E ≃L[ℝ] P × V} {lat : Basis ι ℝ P}
    {r B₀ F₀ F₁ : E → ℝ} {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    {d : OAI.Analysis.PDE.Schauder.InteriorThirdPathData e lat r B₀ F₀ F₁ hΩK} {C B : ℝ}
    (hsolve : UniformPathClassicalEstimate e lat d C) (hC : 0 < C) (hB : 0 < B)
    (hr : ContDiff ℝ 1 r) (hreg : ∀ x, r x=0 → fderiv ℝ r x ≠ 0)
    (hB₀ : ContDiff ℝ 4 B₀) (hF₀ : ContDiff ℝ 2 F₀) (hF₁ : ContDiff ℝ 2 F₁)
    (T S : E → E) (hT : ContDiff ℝ 3 T) (hS : ContDiff ℝ 2 S)
    (hTp : LatticePeriodic e lat T) (hSp : LatticePeriodic e lat S)
    (hTtan : ∀ x, r x=0 → fderiv ℝ r x (T x)=0)
    (hStan : ∀ x, r x=0 → fderiv ℝ r x (S x)=0)
    (hsource : ∀ s : SmoothPathSolution e lat r B₀ F₀ F₁,
      ∃ F : OAI.Analysis.Normed.Function.Holder.LatticeHolderSpace (K := {x | r x ≤ 0}) (α := d.exponent/2) e lat,
        (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value F.val x = mooreSecondBackgroundForcing
          (fun y => B₀ y+s.u y) B₀ (densityPath F₀ F₁ s.t) T S x) ∧ ‖F‖ ≤ B) :
    ∃ M > 0, ∀ s : SmoothPathSolution e lat r B₀ F₀ F₁,
      ∃ U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK (d.exponent/2),
        ‖U‖ ≤ M ∧ U ∈ OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet e lat ∧
        (∀ x : {x | r x ≤ 0}, OAI.Analysis.PDE.Elliptic.fieldDerivative (OAI.Analysis.PDE.Elliptic.fieldDerivative s.u T) S x = OAI.Analysis.Normed.Function.Holder.C2Holder.value U x) ∧
        (∀ x : {x | r x ≤ 0},
          fderiv ℝ (OAI.Analysis.PDE.Elliptic.fieldDerivative (OAI.Analysis.PDE.Elliptic.fieldDerivative s.u T) S) x = OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U x) ∧
        (∀ x : {x | r x ≤ 0},
          fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Elliptic.fieldDerivative (OAI.Analysis.PDE.Elliptic.fieldDerivative s.u T) S)) x =
            OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U x) := by
  refine ⟨C*B,mul_pos hC hB,?_⟩
  intro s
  obtain ⟨F,eF,nF⟩ := hsource s
  exact exists_norm_bound_mono
    (OAI.Analysis.PDE.Dirichlet.UniformPathClassicalEstimate.second_tangent
      (n := n) (e := e) (lat := lat) (r := r) (B₀ := B₀) (F₀ := F₀) (F₁ := F₁)
      (hΩK := hΩK) (d := d) (C := C) hsolve s hr hreg hB₀ hF₀ hF₁
      T S hT hS hTp hSp hTtan hStan F eF)
    (mul_le_mul_of_nonneg_left nF hC.le)

end OAI.Analysis.PDE.Dirichlet
