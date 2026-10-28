import OAI.Analysis.Fourier.WavePackets.TransportRegular
import OAI.Analysis.PDE.Dirichlet.C2HolderQuaternion
import OAI.Analysis.PDE.Dirichlet.ComparisonLocal

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Filter OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Concentration OAI.Analysis.PDE.Green
open scoped Topology ContDiff Matrix.Norms.Elementwise

/-- Joint smoothness supplies continuity of the actual spatial quaternionic
Hessian, including when the parameter and spatial variables have different
dimensions. -/
theorem contDiffAt_family_quaternionHessian
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {m s : ℕ} (slots : Fin s → Quaternion ℝ)
    {f : Z × OAI.Analysis.PDE.Dirichlet.CoordinateSpace m s → ℝ} {p : Z × OAI.Analysis.PDE.Dirichlet.CoordinateSpace m s}
    (hf : ContDiffAt ℝ ∞ f p) :
    ContDiffAt ℝ ∞ (fun q : Z × OAI.Analysis.PDE.Dirichlet.CoordinateSpace m s =>
      OAI.Analysis.PDE.Dirichlet.quaternionHessian slots (fun x => f (q.1,x)) q.2) p := by
  have h := contDiffAt_spatial_fderiv (contDiffAt_spatial_fderiv hf)
  exact (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM slots).contDiff.contDiffAt.comp p h

/-- Chosen global defining-function extensions need not vary continuously.
It suffices that their germs agree with one jointly smooth local formula. -/
theorem continuousOn_family_quaternionHessian_of_germs
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {m s : ℕ} (slots : Fin s → Quaternion ℝ)
    {S : Set (Z × OAI.Analysis.PDE.Dirichlet.CoordinateSpace m s)}
    {f : Z × OAI.Analysis.PDE.Dirichlet.CoordinateSpace m s → ℝ}
    {g : Z → OAI.Analysis.PDE.Dirichlet.CoordinateSpace m s → ℝ}
    (hf : ∀ p ∈ S, ContDiffAt ℝ ∞ f p)
    (hg : ∀ p ∈ S, g p.1 =ᶠ[𝓝 p.2] (fun x => f (p.1,x))) :
    ContinuousOn (fun p : Z × OAI.Analysis.PDE.Dirichlet.CoordinateSpace m s =>
      OAI.Analysis.PDE.Dirichlet.quaternionHessian slots (g p.1) p.2) S := by
  have hc : ContinuousOn (fun p : Z × OAI.Analysis.PDE.Dirichlet.CoordinateSpace m s =>
      OAI.Analysis.PDE.Dirichlet.quaternionHessian slots (fun x => f (p.1,x)) p.2) S :=
    fun p hp => (contDiffAt_family_quaternionHessian slots (hf p hp)).continuousAt.continuousWithinAt
  apply hc.congr
  intro p hp
  exact OAI.Analysis.PDE.Dirichlet.quaternionHessian_congr_germ slots (hg p hp)

/-- The literal rational defining function is jointly smooth at every
closed physical-fiber point in the parameter annulus. -/
theorem contDiffAt_paddedPhysicalDefining_joint (d : ℕ) (a : ℝ)
    (ha : 0 < a) (p : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d+1) 4)
    (hp : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime p.1‖)
    (hx : paddedPhysicalDefining d a (OAI.Analysis.PDE.Green.energyComplexTime p.1) p.2 ≤ 0) :
    ContDiffAt ℝ ∞ (fun q : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d+1) 4 =>
      paddedPhysicalDefining d a (OAI.Analysis.PDE.Green.energyComplexTime q.1) q.2) p := by
  have hreg := OAI.Analysis.Calculus.Current.physical_fiber_collar_subset_regular a (OAI.Analysis.PDE.Green.energyComplexTime p.1) ha hp
    (hx.trans (show (0 : ℝ) ≤ 1 by norm_num))
  have hm : ContDiff ℝ ∞ (fun q : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d+1) 4 =>
      OAI.Analysis.Calculus.Current.physicalEmbedding (OAI.Analysis.PDE.Green.energyComplexTime q.1) (paddedPhysicalSplit d q.2).2) := by
    have hi : ContDiff ℝ ∞ (fun q : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d+1) 4 =>
        (OAI.Analysis.PDE.Green.energyComplexTime q.1,(paddedPhysicalSplit d q.2).2)) :=
      ((OAI.Analysis.PDE.Green.contDiff_energyComplexTime ∞).comp contDiff_fst).prodMk
        (contDiff_snd.comp ((paddedPhysicalSplit d).contDiff.comp contDiff_snd))
    exact (OAI.Analysis.PDE.Green.contDiff_physicalEmbedding_joint d ∞).comp hi
  exact ((OAI.Analysis.Calculus.Current.contDiffAt_fiberDefining (1/10) a _ hreg.1).of_le (by simp)).comp p hm.contDiffAt

end OAI.Analysis.Fourier.WavePackets
