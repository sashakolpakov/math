import OAI.Analysis.PDE.Dirichlet.Rough.Parameter.InverseJets

/-!
Raw coefficients of a locally trivialized moving-domain problem.
All differentiations are on the given open neighborhoods; neither map is
assumed smooth outside its own neighborhood.
-/

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet.ParameterDeformation

variable {Z E F : Type*}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Spatial differentiation preserves joint smoothness on an arbitrary
open subset of parameter-space times physical-space. -/
theorem contDiffOn_slice_fderiv_open {O : Set (Z × E)} (hO : IsOpen O)
    {f : Z × E → F} (hf : ContDiffOn ℝ ∞ f O) :
    ContDiffOn ℝ ∞ (fun p : Z × E => fderiv ℝ (fun y => f (p.1,y)) p.2) O := by
  have hd : ContDiffOn ℝ ∞ (fderiv ℝ f) O :=
    hf.fderiv_of_isOpen hO (by simp)
  apply (hd.clm_comp contDiffOn_const).congr
  intro p hp
  exact ParameterDeformation.fderiv_slice_right_at
    (((hf p hp).contDiffAt (hO.mem_nhds hp)).differentiableAt (by simp))

theorem contDiffOn_slice_second_fderiv_open {O : Set (Z × E)} (hO : IsOpen O)
    {f : Z × E → F} (hf : ContDiffOn ℝ ∞ f O) :
    ContDiffOn ℝ ∞ (fun p : Z × E =>
      fderiv ℝ (fderiv ℝ (fun y => f (p.1,y))) p.2) O := by
  exact ParameterDeformation.contDiffOn_slice_fderiv_open hO (ParameterDeformation.contDiffOn_slice_fderiv_open hO hf)

/-- The first derivative of the local inverse, evaluated at the forward map. -/
def localFamilyJacobian (Φ Ψ : Z × E → E) (p : Z × E) : E →L[ℝ] E :=
  fderiv ℝ (fun y => Ψ (p.1,y)) (Φ p)

/-- The second derivative of the local inverse, including its curvature. -/
def localFamilyCurvature (Φ Ψ : Z × E → E) (p : Z × E) : E →L[ℝ] E →L[ℝ] E :=
  fderiv ℝ (fderiv ℝ (fun y => Ψ (p.1,y))) (Φ p)

/-- The physical background Hessian evaluated at the forward map. -/
def localFamilyBackground (Φ : Z × E → E) (B : Z × E → ℝ)
    (p : Z × E) : E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ (fun y => B (p.1,y))) (Φ p)

theorem contDiffOn_localFamilyJacobian {S T : Set (Z × E)} (hT : IsOpen T)
    {Φ Ψ : Z × E → E} (hΦ : ContDiffOn ℝ ∞ Φ S) (hΨ : ContDiffOn ℝ ∞ Ψ T)
    (hmap : MapsTo (fun p : Z × E => (p.1,Φ p)) S T) :
    ContDiffOn ℝ ∞ (ParameterDeformation.localFamilyJacobian Φ Ψ) S := by
  exact (ParameterDeformation.contDiffOn_slice_fderiv_open hT hΨ).comp (contDiffOn_fst.prodMk hΦ) hmap

theorem contDiffOn_localFamilyCurvature {S T : Set (Z × E)} (hT : IsOpen T)
    {Φ Ψ : Z × E → E} (hΦ : ContDiffOn ℝ ∞ Φ S) (hΨ : ContDiffOn ℝ ∞ Ψ T)
    (hmap : MapsTo (fun p : Z × E => (p.1,Φ p)) S T) :
    ContDiffOn ℝ ∞ (ParameterDeformation.localFamilyCurvature Φ Ψ) S := by
  exact (ParameterDeformation.contDiffOn_slice_second_fderiv_open hT hΨ).comp
    (contDiffOn_fst.prodMk hΦ) hmap

theorem contDiffOn_localFamilyBackground {S T : Set (Z × E)} (hT : IsOpen T)
    {Φ : Z × E → E} {B : Z × E → ℝ}
    (hΦ : ContDiffOn ℝ ∞ Φ S) (hB : ContDiffOn ℝ ∞ B T)
    (hmap : MapsTo (fun p : Z × E => (p.1,Φ p)) S T) :
    ContDiffOn ℝ ∞ (ParameterDeformation.localFamilyBackground Φ B) S := by
  exact (ParameterDeformation.contDiffOn_slice_second_fderiv_open hT hB).comp
    (contDiffOn_fst.prodMk hΦ) hmap

/-- The local inverse identity forces the pulled Jacobian to be onto.
No globally defined inverse or global differentiability is required. -/
theorem localFamilyJacobian_surjective {S T : Set (Z × E)}
    (hS : IsOpen S) (hT : IsOpen T) {Φ Ψ : Z × E → E}
    (hΦ : ContDiffOn ℝ ∞ Φ S) (hΨ : ContDiffOn ℝ ∞ Ψ T)
    (hmap : MapsTo (fun p : Z × E => (p.1,Φ p)) S T)
    {p : Z × E} (hp : p ∈ S)
    (hinv : (fun y => Ψ (p.1,Φ (p.1,y))) =ᶠ[𝓝 p.2] id) :
    Function.Surjective (ParameterDeformation.localFamilyJacobian Φ Ψ p) := by
  have hΦp : DifferentiableAt ℝ (fun y => Φ (p.1,y)) p.2 := by
    apply (((hΦ p hp).contDiffAt (hS.mem_nhds hp)).differentiableAt (by simp)).comp
    exact (show ContDiff ℝ ∞ (fun y : E => (p.1,y)) from
      contDiff_const.prodMk contDiff_id).contDiffAt.differentiableAt (by simp)
  have hΨp : DifferentiableAt ℝ (fun y => Ψ (p.1,y)) (Φ p) := by
    apply (((hΨ _ (hmap hp)).contDiffAt (hT.mem_nhds (hmap hp))).differentiableAt
      (by simp)).comp
    exact (show ContDiff ℝ ∞ (fun y : E => (p.1,y)) from
      contDiff_const.prodMk contDiff_id).contDiffAt.differentiableAt (by simp)
  have he : (ParameterDeformation.localFamilyJacobian Φ Ψ p).comp
      (fderiv ℝ (fun y => Φ (p.1,y)) p.2) = ContinuousLinearMap.id ℝ E := by
    rw [ParameterDeformation.localFamilyJacobian, ← fderiv_comp p.2 hΨp hΦp]
    simpa only [Function.comp_def, fderiv_id] using hinv.fderiv_eq (𝕜 := ℝ)
  intro v
  exact ⟨fderiv ℝ (fun y => Φ (p.1,y)) p.2 v,
    congrArg (fun L : E →L[ℝ] E => L v) he⟩

end OAI.Analysis.PDE.Dirichlet.ParameterDeformation
