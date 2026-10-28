import OAI.Analysis.Fourier.WavePackets.TransportRegular
import OAI.Analysis.Fourier.WavePackets.CalculusPacketPushbackGeometry

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Filter OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Concentration OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green
open scoped Topology ContDiff

/-- The two fiber transports are inverse on a neighborhood of the closed
fiber, not only on the fiber itself. -/
theorem paddedPhysicalTransport_inverse_germ (d : ℕ) (a : ℝ) (τ₀ τ : ℂ)
    (ha : 0 < a) (ht₀ : a ≤ ‖τ₀‖) (ht : a ≤ ‖τ‖)
    {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4} (hx : paddedPhysicalDefining d a τ₀ x ≤ 0) :
    (fun y => paddedPhysicalTransport d a τ τ₀ (paddedPhysicalTransport d a τ₀ τ y))
      =ᶠ[𝓝 x] id := by
  have hr := OAI.Analysis.Calculus.Current.physical_fiber_collar_subset_regular a τ₀ ha ht₀
    (hx.trans (show (0 : ℝ) ≤ 1 by norm_num))
  have hp : Continuous (fun y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4 => (paddedPhysicalSplit d y).2) :=
    continuous_snd.comp (paddedPhysicalSplit d).continuous
  have hc : ContinuousAt (fun y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4 =>
      OAI.Analysis.Calculus.Current.physicalFiberCoordinates a τ₀ (paddedPhysicalSplit d y).2) x := by
    have hc₀ : ContinuousAt (fun q : Option (Fin d) → ℂ => OAI.Analysis.Calculus.Current.physicalFiberCoordinates a τ₀ q)
        (paddedPhysicalSplit d x).2 :=
      (contDiffAt_physicalCoordinates_joint a τ₀ _ hr.1).continuousAt.comp
        (continuousAt_const.prodMk continuousAt_id)
    exact ContinuousAt.comp (g := fun q : Option (Fin d) → ℂ => OAI.Analysis.Calculus.Current.physicalFiberCoordinates a τ₀ q)
      (f := fun y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4 => (paddedPhysicalSplit d y).2)
      (x := x) hc₀ hp.continuousAt
  have hN : ContinuousAt (fun y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4 =>
      Real.sqrt 2 • τ + a • OAI.Analysis.Calculus.Current.physicalFiberCoordinates a τ₀ (paddedPhysicalSplit d y).2 none) x :=
    continuousAt_const.add (((continuous_apply none).continuousAt.comp hc).const_smul a)
  have hu := physicalFiberCoordinates_mem_parameter_ball a τ₀ hx
  filter_upwards [hp.continuousAt.preimage_mem_nhds ((OAI.Analysis.Calculus.Current.isOpen_physicalRegularDomain τ₀).mem_nhds hr),
    hN.eventually_ne (OAI.Analysis.Calculus.Current.fiberParameterBall_numerator a τ ha ht hu)] with y hy hNy
  apply (paddedPhysicalSplit d).injective
  rw [paddedPhysicalTransport_split,paddedPhysicalTransport_split]
  refine Prod.ext rfl ?_
  change OAI.Analysis.Calculus.Current.physicalFiberInverse a τ₀
    (OAI.Analysis.Calculus.Current.physicalFiberCoordinates a τ (OAI.Analysis.Calculus.Current.physicalFiberInverse a τ
      (OAI.Analysis.Calculus.Current.physicalFiberCoordinates a τ₀ (paddedPhysicalSplit d y).2))) = _
  rw [OAI.Analysis.Calculus.Current.physicalCoordinates_right_inverse a τ _ ha.ne' hNy hy.2]
  exact OAI.Analysis.Calculus.Current.physicalCoordinates_left_inverse a τ₀ _ ha.ne' hy.1 hy.2

theorem physicalTransportJ_surjective (d : ℕ) (a : ℝ) (τ₀ τ : ℂ)
    (ha : 0 < a) (ht₀ : a ≤ ‖τ₀‖) (ht : a ≤ ‖τ‖)
    {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4} (hx : paddedPhysicalDefining d a τ₀ x ≤ 0) :
    Function.Surjective (physicalTransportJ d a τ₀ (τ,x)) := by
  have hy : paddedPhysicalDefining d a τ (paddedPhysicalTransport d a τ₀ τ x) ≤ 0 :=
    (paddedPhysicalTransport_defining d a τ₀ τ ha ht hx).trans_le hx
  have hf := (contDiffAt_paddedPhysicalTransport_slice d a τ₀ τ ha ht₀ hx).differentiableAt (by simp)
  have hg := (contDiffAt_paddedPhysicalTransport_slice d a τ τ₀ ha ht hy).differentiableAt (by simp)
  have hcomp := hg.hasFDerivAt.comp x hf.hasFDerivAt
  have hid : HasFDerivAt
      (fun y => paddedPhysicalTransport d a τ τ₀ (paddedPhysicalTransport d a τ₀ τ y))
      (ContinuousLinearMap.id ℝ _) x := (hasFDerivAt_id x).congr_of_eventuallyEq
    (paddedPhysicalTransport_inverse_germ d a τ₀ τ ha ht₀ ht hx)
  have he := hcomp.unique hid
  intro w
  refine ⟨(fderiv ℝ (paddedPhysicalTransport d a τ₀ τ) x) w,?_⟩
  exact congrArg (fun L => L w) he

end OAI.Analysis.Fourier.WavePackets
