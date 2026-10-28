import OAI.Analysis.Fourier.WavePackets.PaddingLattice
import OAI.Analysis.PDE.Dirichlet.ContinuousComparison
import OAI.Analysis.PDE.Dirichlet.Translation

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Module OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped ContDiff ComplexOrder

theorem latticePeriodic_translate {E P V W ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) {f : E → W}
    (hf : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b f) (c : E) : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => f (c + x)) := by
  intro x l
  have he : c + e.symm ((e x).1 + (l : P), (e x).2) =
      e.symm ((e (c + x)).1 + (l : P), (e (c + x)).2) := by
    apply e.injective
    simp only [map_add, ContinuousLinearEquiv.apply_symm_apply, Prod.fst_add, Prod.snd_add]
    apply Prod.ext <;> simp [add_assoc]
  simpa only [he] using hf (c + x) l

/-- Uniqueness forces a periodic Dirichlet solution to inherit any
translation symmetry of its domain, background, and density. -/
theorem dirichlet_translation_invariance {m : ℕ} (hm : 1 ≤ m)
    {P V ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
    (e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4 ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    {C : Set V} (hC : IsCompact C) {r B F u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4 → ℝ}
    (hr : ContDiff ℝ 2 r) (hB : ContDiff ℝ 2 B) (hu : ContDiff ℝ 2 u)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ C)
    (hrper : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r) (hBper : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b B)
    (huper : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b u)
    (hrpos : ∀ x, r x < 0 → (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef)
    (hupos : ∀ x, r x < 0 →
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y => B y + u y) x)).PosDef)
    (heq : ∀ x, r x < 0 → OAI.LinearAlgebra.Moore.mooreDet m
      (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y => B y + u y) x) = F x)
    (hzero : ∀ x, r x = 0 → u x = 0)
    (c : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4)
    (hrc : ∀ x, r (c + x) = r x) (hBc : ∀ x, B (c + x) = B x)
    (hFc : ∀ x, F (c + x) = F x) :
    ∀ x, r x ≤ 0 → u (c + x) = u x := by
  let v := fun x => B x + u x
  have hv : ContDiff ℝ 2 v := hB.add hu
  have hvc : ContDiff ℝ 2 (fun x => v (c + x)) := hv.comp (contDiff_const.add contDiff_id)
  have hpv : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b v := hBper.add huper
  have hpositive : ∀ x, r x < 0 →
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y => v (c + y)) x)).PosDef := by
    intro x hx
    rw [OAI.Analysis.PDE.Dirichlet.quaternionHessian_translation]
    exact hupos _ (by simpa only [hrc] using hx)
  have hdet : ∀ x, r x < 0 → OAI.LinearAlgebra.Moore.mooreDet m
      (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y => v (c + y)) x) =
        OAI.LinearAlgebra.Moore.mooreDet m (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots v x) := by
    intro x hx
    rw [OAI.Analysis.PDE.Dirichlet.quaternionHessian_translation, heq _ (by simpa only [hrc] using hx), heq _ hx, hFc]
  have hbd : ∀ x, r x = 0 → v (c + x) = v x := by
    intro x hx
    simp only [v, hBc, hzero x hx, hzero (c + x) (by simpa only [hrc] using hx)]
  have huniq := OAI.Analysis.PDE.Dirichlet.quaternionic_dirichlet_uniqueness_continuous_lattice hm e b hC
    hvc.contDiffOn hv.contDiffOn hr hvc.continuous.continuousOn hv.continuous.continuousOn
    hbounded hrper (latticePeriodic_translate e b hpv c) hpv hrpos hpositive hupos hdet hbd
  intro x hx
  have he := huniq x hx
  simpa only [v, hBc, add_right_inj] using he

end OAI.Analysis.Fourier.WavePackets
