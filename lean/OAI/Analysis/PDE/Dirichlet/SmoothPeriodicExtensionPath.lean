import OAI.Analysis.Calculus.SmoothExtension.Periodic.Extension.Regular
import OAI.Analysis.Normed.Function.Holder.SmoothPeriodicExtensionJets
import OAI.Analysis.PDE.Weak.PeriodicDirichletSublevel
import OAI.Analysis.PDE.Dirichlet.Path.LimitData

/-! Upgrading the actual closed-domain path limit to a genuine global
periodic C⁴ solution, once its one-sided C⁴ regularity has been proved. -/

noncomputable section
open Set Module
open scoped ContDiff Matrix.Norms.Elementwise ComplexOrder
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore OAI.Analysis.Normed.Function.Holder OAI.Analysis.Calculus.SmoothExtension

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

theorem BanachPathLimit.exists_smoothPathSolution_of_closed_contDiff
    (hn : 1 ≤ n) (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    {C : Set V} (hC : IsCompact C)
    {r B₀ F₀ F₁ : CoordinateSpace n 4 → ℝ}
    (hr : ContDiff ℝ ∞ r) (hrp : LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ C)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hB₀ : ContDiff ℝ 4 B₀) (hB₀p : LatticePeriodic e b B₀)
    {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}} {β : ℝ}
    {s : ℕ → SmoothPathSolution e b r B₀ F₀ F₁} {t : ℝ}
    (L : BanachPathLimit e b r B₀ F₀ F₁ hΩD β s t) (ht : t ∈ Icc (0 : ℝ) 1)
    (hfour : ContDiffOn ℝ 4 (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value L.value))
      {x | r x ≤ 0}) :
    ∃ S : SmoothPathSolution e b r B₀ F₀ F₁, S.t = t ∧
      ∀ x : {x | r x ≤ 0}, B₀ x + S.u x = OAI.Analysis.Normed.Function.Holder.C2Holder.value L.value x := by
  obtain ⟨g, hg, hgp, hgeq⟩ := OAI.Analysis.Calculus.SmoothExtension.exists_latticePeriodic_extension_regular_sublevel_equiv
    (m := n*4) (by omega) (flattenFourSlots n).symm.toContinuousLinearEquiv e b hC
    r hr hrp hbounded hreg (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value L.value)) L.periodic hfour
  have heq : ∀ x : {x | r x ≤ 0}, g x = OAI.Analysis.Normed.Function.Holder.C2Holder.value L.value x := by
    intro x
    simpa only [OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply _ x.property] using hgeq x x.property
  have hclosure : {x | r x ≤ 0} ⊆ closure {x | r x < 0} := by
    rw [OAI.Analysis.PDE.Weak.closure_strict_sublevel_of_regular r (hr.of_le (by simp)) hreg]
  have hjets := OAI.Analysis.Normed.Function.Holder.C2Holder.classical_extension_derivatives
    (isOpen_lt hr.continuous continuous_const) hclosure L.value g
    (hg.of_le (by norm_num)) heq
  have hfield (x : {x | r x ≤ 0}) :
      OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩD β OAI.Analysis.Calculus.Quaternion.fourSlots L.value) x =
        quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g x :=
    quaternionHessianField_eq_of_secondDerivative_eq OAI.Analysis.Calculus.Quaternion.fourSlots L.value g x (hjets.2 x).symm
  have hactual (x : {x | r x ≤ 0}) :
      OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g x) = densityPath F₀ F₁ t x ∧
        (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g x)).PosDef := by
    simpa only [hfield x] using L.admissible x
  have hfun : (fun y => B₀ y + (g y - B₀ y)) = g := by
    funext y
    ring
  refine ⟨{
    t := t
    parameter := ht
    u := fun x => g x - B₀ x
    smooth := hg.sub hB₀
    periodic := ?_
    zero := ?_
    positive := ?_
    equation := ?_
  }, rfl, ?_⟩
  · intro x l
    change g (e.symm ((e x).1 + (l : P), (e x).2)) -
      B₀ (e.symm ((e x).1 + (l : P), (e x).2)) = g x - B₀ x
    rw [hgp x l, hB₀p x l]
  · intro x hx
    exact sub_eq_zero.mpr ((heq ⟨x, hx.le⟩).trans (L.boundary ⟨x, hx.le⟩ hx))
  · intro x hx
    rw [hfun]
    exact (hactual ⟨x, hx.le⟩).2
  · intro x hx
    rw [hfun]
    exact (hactual ⟨x, hx.le⟩).1
  · intro x
    change B₀ x + (g x - B₀ x) = OAI.Analysis.Normed.Function.Holder.C2Holder.value L.value x
    calc
      B₀ x + (g x - B₀ x) = g x := by ring
      _ = OAI.Analysis.Normed.Function.Holder.C2Holder.value L.value x := heq x

end OAI.Analysis.PDE.Dirichlet
