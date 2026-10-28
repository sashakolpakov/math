import OAI.Analysis.Fourier.WavePackets.TransportJets

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Filter OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Concentration OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green
open scoped Topology ContDiff

theorem isOpen_jointPhysicalRegular (d : ℕ) :
    IsOpen {p : ℂ × (Option (Fin d) → ℂ) | p.2 ∈ OAI.Analysis.Calculus.Current.physicalRegularDomain p.1} := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  have hY : ContinuousAt (fun q : ℂ × (Option (Fin d) → ℂ) => OAI.Analysis.Calculus.Current.physicalEmbedding q.1 q.2 none) p := by
    exact ((continuous_apply none).comp (OAI.Analysis.PDE.Green.contDiff_physicalEmbedding_joint d ∞).continuous).continuousAt
  have hD : ContinuousAt (fun q : ℂ × (Option (Fin d) → ℂ) =>
      OAI.Analysis.Calculus.Current.fiberDenominator (OAI.Analysis.Calculus.Current.ratio (OAI.Analysis.Calculus.Current.physicalEmbedding q.1 q.2))) p := by
    have hc : ContDiffAt ℝ ∞ (fun z : OAI.Analysis.Calculus.Current.Index d → ℂ => OAI.Analysis.Calculus.Current.fiberDenominator (OAI.Analysis.Calculus.Current.ratio z))
        (OAI.Analysis.Calculus.Current.physicalEmbedding p.1 p.2) := by
      have hs : ContDiffAt ℝ ∞ (fun z : OAI.Analysis.Calculus.Current.Index d → ℂ => OAI.Analysis.Calculus.Current.fiberQuadratic (OAI.Analysis.Calculus.Current.ratio z))
          (OAI.Analysis.Calculus.Current.physicalEmbedding p.1 p.2) := by
        apply ContDiffAt.sum
        intro i _
        exact ((OAI.Analysis.Calculus.Current.contDiffAt_ratio _ hp.1 i).mul (OAI.Analysis.Calculus.Current.contDiffAt_ratio _ hp.1 i)).of_le (by simp)
      exact contDiffAt_const.add (hs.div_const 2)
    exact (hc.comp p (OAI.Analysis.PDE.Green.contDiff_physicalEmbedding_joint d ∞).contDiffAt).continuousAt
  exact inter_mem (hY.eventually_ne hp.1) (hD.eventually_ne hp.2)

theorem contDiffAt_physicalFiberTransport_regular {d : ℕ} (a : ℝ) (τ₀ τ : ℂ)
    {q : Option (Fin d) → ℂ} (hq : q ∈ OAI.Analysis.Calculus.Current.physicalRegularDomain τ₀) :
    ContDiffAt ℝ ∞ (fun p : ℂ × (Option (Fin d) → ℂ) => physicalFiberTransport a τ₀ p.1 p.2)
      (τ,q) := by
  have hc := (contDiffAt_physicalCoordinates_joint a τ₀ q hq.1).comp (τ,q)
    (contDiffAt_const.prodMk contDiffAt_snd)
  have hD : OAI.Analysis.Calculus.Current.fiberDenominator (fun i => OAI.Analysis.Calculus.Current.physicalFiberCoordinates a τ₀ q (some i)) ≠ 0 := hq.2
  exact (((OAI.Analysis.Calculus.Current.contDiffAt_physicalFiberInverse_joint a τ _ hD).restrict_scalars ℝ).of_le (by simp)).comp
    (τ,q) (contDiffAt_fst.prodMk hc)

theorem contDiffAt_physicalFiberTransport_reverse_regular {d : ℕ} (a : ℝ) (τ₀ τ : ℂ)
    {q : Option (Fin d) → ℂ} (hq : q ∈ OAI.Analysis.Calculus.Current.physicalRegularDomain τ) :
    ContDiffAt ℝ ∞ (fun p : ℂ × (Option (Fin d) → ℂ) => physicalFiberTransport a p.1 τ₀ p.2)
      (τ,q) := by
  have hD : OAI.Analysis.Calculus.Current.fiberDenominator (fun i => OAI.Analysis.Calculus.Current.physicalFiberCoordinates a τ q (some i)) ≠ 0 := hq.2
  exact (((OAI.Analysis.Calculus.Current.contDiffAt_physicalFiberInverse a τ₀ _ hD).restrict_scalars ℝ).of_le (by simp)).comp
    (τ,q) (contDiffAt_physicalCoordinates_joint a τ q hq.1)

theorem contDiffAt_paddedPhysicalTransport_regular (d : ℕ) (a : ℝ) (τ₀ τ : ℂ)
    {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4} (hx : (paddedPhysicalSplit d x).2 ∈ OAI.Analysis.Calculus.Current.physicalRegularDomain τ₀) :
    ContDiffAt ℝ ∞ (fun p : ℂ × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4 =>
      paddedPhysicalTransport d a τ₀ p.1 p.2) (τ,x) := by
  have hp : ContDiff ℝ ∞ (fun p : ℂ × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4 =>
      (p.1, (paddedPhysicalSplit d p.2).2)) := by fun_prop
  have hq := (contDiffAt_physicalFiberTransport_regular a τ₀ τ hx).comp (τ,x) hp.contDiffAt
  have hr : ContDiff ℝ ∞ (fun p : ℂ × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4 =>
      (paddedPhysicalSplit d p.2).1) := by fun_prop
  exact (paddedPhysicalSplit d).symm.contDiff.contDiffAt.comp (τ,x) (hr.contDiffAt.prodMk hq)

theorem contDiffAt_paddedPhysicalTransport_reverse_regular (d : ℕ) (a : ℝ) (τ₀ τ : ℂ)
    {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4} (hx : (paddedPhysicalSplit d x).2 ∈ OAI.Analysis.Calculus.Current.physicalRegularDomain τ) :
    ContDiffAt ℝ ∞ (fun p : ℂ × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4 =>
      paddedPhysicalTransport d a p.1 τ₀ p.2) (τ,x) := by
  have hp : ContDiff ℝ ∞ (fun p : ℂ × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4 =>
      (p.1, (paddedPhysicalSplit d p.2).2)) := by fun_prop
  have hq := (contDiffAt_physicalFiberTransport_reverse_regular a τ₀ τ hx).comp (τ,x) hp.contDiffAt
  have hr : ContDiff ℝ ∞ (fun p : ℂ × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4 =>
      (paddedPhysicalSplit d p.2).1) := by fun_prop
  exact (paddedPhysicalSplit d).symm.contDiff.contDiffAt.comp (τ,x) (hr.contDiffAt.prodMk hq)

def transportRegularDomain (d : ℕ) (a : ℝ) (τ₀ : ℂ) :
    Set (ℂ × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4) :=
  {p | (paddedPhysicalSplit d p.2).2 ∈ OAI.Analysis.Calculus.Current.physicalRegularDomain τ₀ ∧
    (paddedPhysicalSplit d (paddedPhysicalTransport d a τ₀ p.1 p.2)).2 ∈ OAI.Analysis.Calculus.Current.physicalRegularDomain p.1}

theorem isOpen_transportRegularDomain (d : ℕ) (a : ℝ) (τ₀ : ℂ) :
    IsOpen (transportRegularDomain d a τ₀) := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  have hsource : IsOpen {q : ℂ × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4 |
      (paddedPhysicalSplit d q.2).2 ∈ OAI.Analysis.Calculus.Current.physicalRegularDomain τ₀} :=
    (OAI.Analysis.Calculus.Current.isOpen_physicalRegularDomain τ₀).preimage (by fun_prop)
  have htarget : ContinuousAt (fun q : ℂ × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4 =>
      (q.1, (paddedPhysicalSplit d (paddedPhysicalTransport d a τ₀ q.1 q.2)).2)) p := by
    exact continuousAt_fst.prodMk
      ((continuous_snd.comp (paddedPhysicalSplit d).continuous).continuousAt.comp
        (contDiffAt_paddedPhysicalTransport_regular d a τ₀ p.1 hp.1).continuousAt)
  exact inter_mem (hsource.mem_nhds hp.1)
    (htarget.preimage_mem_nhds ((isOpen_jointPhysicalRegular d).mem_nhds hp.2))

theorem closedFiber_mem_transportRegularDomain (d : ℕ) (a : ℝ) (τ₀ τ : ℂ)
    (ha : 0 < a) (ht₀ : a ≤ ‖τ₀‖) (ht : a ≤ ‖τ‖)
    {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4} (hx : paddedPhysicalDefining d a τ₀ x ≤ 0) :
    (τ,x) ∈ transportRegularDomain d a τ₀ := by
  constructor
  · exact OAI.Analysis.Calculus.Current.physical_fiber_collar_subset_regular a τ₀ ha ht₀
      (hx.trans (show (0 : ℝ) ≤ 1 by norm_num))
  · have hy : paddedPhysicalDefining d a τ (paddedPhysicalTransport d a τ₀ τ x) ≤ 0 := by
      rwa [paddedPhysicalTransport_defining d a τ₀ τ ha ht hx]
    exact OAI.Analysis.Calculus.Current.physical_fiber_collar_subset_regular a τ ha ht
      (hy.trans (show (0 : ℝ) ≤ 1 by norm_num))

theorem contDiffOn_physicalTransportJ (d : ℕ) (a : ℝ) (τ₀ : ℂ) :
    ContDiffOn ℝ ∞ (physicalTransportJ d a τ₀) (transportRegularDomain d a τ₀) := by
  intro p hp
  have hr := contDiffAt_spatial_fderiv
    (contDiffAt_paddedPhysicalTransport_reverse_regular d a τ₀ p.1 hp.2)
  exact (hr.comp p (contDiffAt_fst.prodMk
    (contDiffAt_paddedPhysicalTransport_regular d a τ₀ p.1 hp.1))).contDiffWithinAt

theorem contDiffOn_physicalTransportK (d : ℕ) (a : ℝ) (τ₀ : ℂ) :
    ContDiffOn ℝ ∞ (physicalTransportK d a τ₀) (transportRegularDomain d a τ₀) := by
  intro p hp
  have hr := contDiffAt_spatial_fderiv (contDiffAt_spatial_fderiv
    (contDiffAt_paddedPhysicalTransport_reverse_regular d a τ₀ p.1 hp.2))
  exact (hr.comp p (contDiffAt_fst.prodMk
    (contDiffAt_paddedPhysicalTransport_regular d a τ₀ p.1 hp.1))).contDiffWithinAt

end OAI.Analysis.Fourier.WavePackets
