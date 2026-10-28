import OAI.Analysis.PDE.Schauder.Calculus.Periodic.HolderSmooth

open Set Module
open scoped ContDiff
noncomputable section
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Normed.Function.Holder

variable {E P V I : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype I]

/-- Hölder-valued coefficients of a boundary-preserving coordinate change.
The background Hessian is evaluated at the changed point, while all unknown
jets will be evaluated at the original point. -/
structure DeformationFields (r : E → ℝ) (α : ℝ) (U : Set ℝ)
    (Φ : ℝ × E → E) (B₀ f : E → ℝ) where
  jacobian : ℝ → OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] E) α
  curvature : ℝ → OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] E →L[ℝ] E) α
  background : ℝ → OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] E →L[ℝ] ℝ) α
  source : ℝ → OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} ℝ α
  jacobian_smooth : ContDiffOn ℝ ∞ jacobian U
  curvature_smooth : ContDiffOn ℝ ∞ curvature U
  background_smooth : ContDiffOn ℝ ∞ background U
  source_smooth : ContDiffOn ℝ ∞ source U
  jacobian_value : ∀ t ∈ U, ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (jacobian t) x = OAI.Analysis.PDE.Dirichlet.inverseJacobian Φ (t,x)
  curvature_value : ∀ t ∈ U, ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (curvature t) x = OAI.Analysis.PDE.Dirichlet.inverseHessian Φ (t,x)
  background_value : ∀ t ∈ U, ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (background t) x =
    fderiv ℝ (fderiv ℝ B₀) (Φ (t,x))
  source_value : ∀ t ∈ U, ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (source t) x = f (Φ (t,x))

omit [ProperSpace E] [Fintype I] in
theorem latticePeriodic_comp_equivariant {F : Type*}
    (e : E ≃L[ℝ] P × V) (b : Basis I ℝ P) {g : E → F} (hg : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b g)
    (φ : E → E) (hφ : ∀ l : Submodule.span ℤ (Set.range b), ∀ x,
      φ (x+e.symm ((l:P),0)) = φ x+e.symm ((l:P),0)) :
    OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (g ∘ φ) := by
  intro x l
  change g (φ (e.symm ((e x).1+(l:P),(e x).2))) = g (φ x)
  rw [OAI.Analysis.PDE.Dirichlet.lattice_translate_eq,add_comm (e.symm ((l:P),0)) x,hφ l]
  have h := hg (φ x) l
  simpa only [OAI.Analysis.PDE.Dirichlet.lattice_translate_eq,add_comm (e.symm ((l:P),0)) (φ x)] using h

theorem nonempty_deformationFields
    (e : E ≃L[ℝ] P × V) (b : Basis I ℝ P) {K : Set V} (hK : IsCompact K)
    {r : E → ℝ} (hr : Continuous r) (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) {U : Set ℝ} (hU : IsOpen U)
    (Φ : ℝ × E → E) (hΦ : ContDiff ℝ ∞ Φ)
    (hi : ContDiffOn ℝ ∞ (fun p : ℝ × E => OAI.Analysis.PDE.Dirichlet.inverseFamily Φ p.1 p.2) {p | p.1 ∈ U})
    (hbij : ∀ t ∈ U, Function.Bijective (fun x => Φ (t,x)))
    (hper : ∀ t ∈ U, ∀ l : Submodule.span ℤ (Set.range b), ∀ x,
      Φ (t,x+e.symm ((l:P),0)) = Φ (t,x)+e.symm ((l:P),0))
    (B₀ f : E → ℝ) (hB₀ : ContDiff ℝ ∞ B₀) (hf : ContDiff ℝ ∞ f)
    (hpB : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fderiv ℝ (fderiv ℝ B₀))) (hpf : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b f) :
    Nonempty (DeformationFields r α U Φ B₀ f) := by
  have hJ := OAI.Analysis.PDE.Dirichlet.contDiffOn_inverseJacobian hU hΦ hi
  have hT := OAI.Analysis.PDE.Dirichlet.contDiffOn_inverseHessian hU hΦ hi
  have hpJ t (ht : t ∈ U) : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => OAI.Analysis.PDE.Dirichlet.inverseJacobian Φ (t,x)) := by
    intro x l
    rw [OAI.Analysis.PDE.Dirichlet.lattice_translate_eq,add_comm (e.symm ((l:P),0)) x]
    exact OAI.Analysis.PDE.Dirichlet.inverseJacobian_periodic t (hbij t ht) _ (hper t ht l) x
  have hpT t (ht : t ∈ U) : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => OAI.Analysis.PDE.Dirichlet.inverseHessian Φ (t,x)) := by
    intro x l
    rw [OAI.Analysis.PDE.Dirichlet.lattice_translate_eq,add_comm (e.symm ((l:P),0)) x]
    exact OAI.Analysis.PDE.Dirichlet.inverseHessian_periodic t (hbij t ht) _ (hper t ht l) x
  have hBB : ContDiff ℝ ∞ (fun p => fderiv ℝ (fderiv ℝ B₀) (Φ p)) :=
    ((hB₀.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)).comp hΦ
  obtain ⟨J,hJs,hJv⟩ := exists_smooth_periodic_holder_family e b hK hr hrp hbounded hα hα1 hU
    (OAI.Analysis.PDE.Dirichlet.inverseJacobian Φ) hJ hpJ
  obtain ⟨T,hTs,hTv⟩ := exists_smooth_periodic_holder_family e b hK hr hrp hbounded hα hα1 hU
    (OAI.Analysis.PDE.Dirichlet.inverseHessian Φ) hT hpT
  obtain ⟨B,hBs,hBv⟩ := exists_smooth_periodic_holder_family e b hK hr hrp hbounded hα hα1 hU
    (fun p => fderiv ℝ (fderiv ℝ B₀) (Φ p)) hBB.contDiffOn
    (fun t ht => latticePeriodic_comp_equivariant e b hpB _ (hper t ht))
  obtain ⟨F,hFs,hFv⟩ := exists_smooth_periodic_holder_family e b hK hr hrp hbounded hα hα1 hU
    (fun p => f (Φ p)) (hf.comp hΦ).contDiffOn
    (fun t ht => latticePeriodic_comp_equivariant e b hpf _ (hper t ht))
  exact ⟨⟨J,T,B,F,hJs,hTs,hBs,hFs,hJv,hTv,hBv,hFv⟩⟩

end OAI.Analysis.PDE.Schauder
