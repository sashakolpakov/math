import OAI.Analysis.Fourier.WavePackets.PaddedTrivialization

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Filter OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Concentration OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green
open scoped Topology ContDiff

/-- The physical transport commutes with every translation in both real
periodic factors, not merely with a selected lattice basis. -/
theorem paddedPhysicalTransport_add (d : ℕ) (a : ℝ) (τ₀ τ : ℂ)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4)
    (p : (Fin (d + 1) → ℝ) × (Fin (d + 1) → ℝ)) :
    paddedPhysicalTransport d a τ₀ τ (x + (paddedPhysicalSplit d).symm (p,0)) =
      paddedPhysicalTransport d a τ₀ τ x + (paddedPhysicalSplit d).symm (p,0) := by
  apply (paddedPhysicalSplit d).injective
  simp only [paddedPhysicalTransport_split, map_add, ContinuousLinearEquiv.apply_symm_apply,
    Prod.fst_add, Prod.snd_add, Prod.mk_add_mk, add_zero]

/-- The base transport is the identity as a germ even at the spatial
boundary. This is stronger than equality restricted to the closed fiber. -/
theorem paddedPhysicalTransport_self_germ (d : ℕ) (a : ℝ) (τ : ℂ)
    (ha : 0 < a) (ht : a ≤ ‖τ‖) {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4}
    (hx : paddedPhysicalDefining d a τ x ≤ 0) :
    paddedPhysicalTransport d a τ τ =ᶠ[𝓝 x] id := by
  have hreg := OAI.Analysis.Calculus.Current.physical_fiber_collar_subset_regular a τ ha ht
    (hx.trans (show (0 : ℝ) ≤ 1 by norm_num))
  have hp : Continuous (fun y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4 => (paddedPhysicalSplit d y).2) :=
    continuous_snd.comp (paddedPhysicalSplit d).continuous
  have hn := hp.continuousAt.preimage_mem_nhds ((OAI.Analysis.Calculus.Current.isOpen_physicalRegularDomain τ).mem_nhds hreg)
  filter_upwards [hn] with y hy
  apply (paddedPhysicalSplit d).injective
  rw [paddedPhysicalTransport_split]
  exact Prod.ext rfl (OAI.Analysis.Calculus.Current.physicalCoordinates_left_inverse a τ _ ha.ne' hy.1 hy.2)

theorem paddedPhysicalTransport_self_fderiv (d : ℕ) (a : ℝ) (τ : ℂ)
    (ha : 0 < a) (ht : a ≤ ‖τ‖) {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4}
    (hx : paddedPhysicalDefining d a τ x ≤ 0) :
    fderiv ℝ (paddedPhysicalTransport d a τ τ) x = ContinuousLinearMap.id ℝ _ := by
  rw [(paddedPhysicalTransport_self_germ d a τ ha ht hx).fderiv_eq, fderiv_id]

theorem paddedPhysicalTransport_self_second_fderiv (d : ℕ) (a : ℝ) (τ : ℂ)
    (ha : 0 < a) (ht : a ≤ ‖τ‖) {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4}
    (hx : paddedPhysicalDefining d a τ x ≤ 0) :
    fderiv ℝ (fderiv ℝ (paddedPhysicalTransport d a τ τ)) x = 0 := by
  rw [((paddedPhysicalTransport_self_germ d a τ ha ht hx).fderiv (𝕜 := ℝ)).fderiv_eq]
  have he : fderiv ℝ (id : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4 → OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4) =
      fun _ => ContinuousLinearMap.id ℝ (OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4) := funext (fun _ => fderiv_id)
  rw [he]
  exact (hasFDerivAt_const (ContinuousLinearMap.id ℝ (OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4)) x).fderiv

def physicalTransportJ (d : ℕ) (a : ℝ) (τ₀ : ℂ)
    (p : ℂ × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4) :
    OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4 :=
  fderiv ℝ (paddedPhysicalTransport d a p.1 τ₀) (paddedPhysicalTransport d a τ₀ p.1 p.2)

def physicalTransportK (d : ℕ) (a : ℝ) (τ₀ : ℂ)
    (p : ℂ × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4) :
    OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4 :=
  fderiv ℝ (fderiv ℝ (paddedPhysicalTransport d a p.1 τ₀)) (paddedPhysicalTransport d a τ₀ p.1 p.2)

theorem physicalTransportJ_base (d : ℕ) (a : ℝ) (τ : ℂ)
    (ha : 0 < a) (ht : a ≤ ‖τ‖) {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4}
    (hx : paddedPhysicalDefining d a τ x ≤ 0) :
    physicalTransportJ d a τ (τ,x) = ContinuousLinearMap.id ℝ _ := by
  unfold physicalTransportJ
  rw [paddedPhysicalTransport_self d a τ ha ht hx]
  exact paddedPhysicalTransport_self_fderiv d a τ ha ht hx

theorem physicalTransportK_base (d : ℕ) (a : ℝ) (τ : ℂ)
    (ha : 0 < a) (ht : a ≤ ‖τ‖) {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4}
    (hx : paddedPhysicalDefining d a τ x ≤ 0) :
    physicalTransportK d a τ (τ,x) = 0 := by
  unfold physicalTransportK
  rw [paddedPhysicalTransport_self d a τ ha ht hx]
  exact paddedPhysicalTransport_self_second_fderiv d a τ ha ht hx

theorem contDiffAt_spatial_fderiv {Z E F : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Z × E → F} {p : Z × E} (hf : ContDiffAt ℝ ∞ f p) :
    ContDiffAt ℝ ∞ (fun q : Z × E => fderiv ℝ (fun y => f (q.1,y)) q.2) p := by
  have hg : ContDiffAt ℝ ∞ (fun q : (Z × E) × E => f (q.1.1,q.2)) (p,p.2) :=
    hf.comp (p,p.2) ((contDiffAt_fst.comp (p,p.2) contDiffAt_fst).prodMk contDiffAt_snd)
  exact hg.fderiv contDiffAt_snd (by simp)

theorem contDiffAt_physicalTransportJ (d : ℕ) (a : ℝ) (τ₀ τ : ℂ)
    (ha : 0 < a) (ht₀ : a ≤ ‖τ₀‖) (ht : a ≤ ‖τ‖)
    {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4} (hx : paddedPhysicalDefining d a τ₀ x ≤ 0) :
    ContDiffAt ℝ ∞ (physicalTransportJ d a τ₀) (τ,x) := by
  have hy : paddedPhysicalDefining d a τ (paddedPhysicalTransport d a τ₀ τ x) ≤ 0 := by
    rwa [paddedPhysicalTransport_defining d a τ₀ τ ha ht hx]
  have hr := contDiffAt_spatial_fderiv
    (contDiffAt_paddedPhysicalTransport_reverse_joint d a τ₀ τ ha ht hy)
  exact hr.comp (τ,x) (contDiffAt_fst.prodMk
    (contDiffAt_paddedPhysicalTransport_joint d a τ₀ τ ha ht₀ hx))

theorem contDiffAt_physicalTransportK (d : ℕ) (a : ℝ) (τ₀ τ : ℂ)
    (ha : 0 < a) (ht₀ : a ≤ ‖τ₀‖) (ht : a ≤ ‖τ‖)
    {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4} (hx : paddedPhysicalDefining d a τ₀ x ≤ 0) :
    ContDiffAt ℝ ∞ (physicalTransportK d a τ₀) (τ,x) := by
  have hy : paddedPhysicalDefining d a τ (paddedPhysicalTransport d a τ₀ τ x) ≤ 0 := by
    rwa [paddedPhysicalTransport_defining d a τ₀ τ ha ht hx]
  have hr := contDiffAt_spatial_fderiv (contDiffAt_spatial_fderiv
    (contDiffAt_paddedPhysicalTransport_reverse_joint d a τ₀ τ ha ht hy))
  exact hr.comp (τ,x) (contDiffAt_fst.prodMk
    (contDiffAt_paddedPhysicalTransport_joint d a τ₀ τ ha ht₀ hx))

theorem paddedPhysicalTransport_fderiv_add (d : ℕ) (a : ℝ) (τ₀ τ : ℂ)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4)
    (p : (Fin (d + 1) → ℝ) × (Fin (d + 1) → ℝ)) :
    fderiv ℝ (paddedPhysicalTransport d a τ₀ τ) (x + (paddedPhysicalSplit d).symm (p,0)) =
      fderiv ℝ (paddedPhysicalTransport d a τ₀ τ) x := by
  rw [← fderiv_comp_add_right]
  have he := funext (fun y => paddedPhysicalTransport_add d a τ₀ τ y p)
  rw [he, fderiv_add_const]

theorem paddedPhysicalTransport_second_fderiv_add (d : ℕ) (a : ℝ) (τ₀ τ : ℂ)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4)
    (p : (Fin (d + 1) → ℝ) × (Fin (d + 1) → ℝ)) :
    fderiv ℝ (fderiv ℝ (paddedPhysicalTransport d a τ₀ τ))
        (x + (paddedPhysicalSplit d).symm (p,0)) =
      fderiv ℝ (fderiv ℝ (paddedPhysicalTransport d a τ₀ τ)) x := by
  rw [← fderiv_comp_add_right]
  exact congrArg (fun f => fderiv ℝ f x)
    (funext (fun y => paddedPhysicalTransport_fderiv_add d a τ₀ τ y p))

theorem physicalTransportJ_add (d : ℕ) (a : ℝ) (τ₀ τ : ℂ)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4)
    (p : (Fin (d + 1) → ℝ) × (Fin (d + 1) → ℝ)) :
    physicalTransportJ d a τ₀ (τ, x + (paddedPhysicalSplit d).symm (p,0)) =
      physicalTransportJ d a τ₀ (τ,x) := by
  simp only [physicalTransportJ, paddedPhysicalTransport_add,
    paddedPhysicalTransport_fderiv_add]

theorem physicalTransportK_add (d : ℕ) (a : ℝ) (τ₀ τ : ℂ)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4)
    (p : (Fin (d + 1) → ℝ) × (Fin (d + 1) → ℝ)) :
    physicalTransportK d a τ₀ (τ, x + (paddedPhysicalSplit d).symm (p,0)) =
      physicalTransportK d a τ₀ (τ,x) := by
  simp only [physicalTransportK, paddedPhysicalTransport_add,
    paddedPhysicalTransport_second_fderiv_add]

end OAI.Analysis.Fourier.WavePackets
