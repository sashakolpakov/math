import OAI.Analysis.Fourier.WavePackets.Rough.Packet.DescendedSlice
import OAI.Analysis.PDE.Concentration.FullSplit

noncomputable section
open Set Filter Module
open scoped Topology ContDiff
namespace OAI.Analysis.Fourier.WavePackets

open OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Concentration OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green

def unpadPacketFunction (d : ℕ)
    (g : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4 → ℝ)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) : ℝ :=
  g ((OAI.Analysis.PDE.Concentration.timeSpaceSplit (d + 1) 3 x).1,
    insertFourth (d + 1) (OAI.Analysis.PDE.Concentration.timeSpaceSplit (d + 1) 3 x).2)

theorem unpadPacketFunction_fiber (d : ℕ)
    (g : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4 → ℝ)
    (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) (y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3) :
    unpadPacketFunction d g (OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z y) =
      g (z,insertFourth (d + 1) y) := by
  rw [unpadPacketFunction, ← OAI.Analysis.PDE.Concentration.timeSpaceSplit_symm, ContinuousLinearEquiv.apply_symm_apply]

theorem unpadPacketFunction_smooth {d : ℕ} {a : ℝ}
    {g : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4 → ℝ}
    (hg : ContDiffOn ℝ ∞ g (OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a ×ˢ univ)) :
    OAI.Analysis.PDE.Concentration.PacketLocalSmooth d a (unpadPacketFunction d g) := by
  let Q : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4 :=
    fun x ↦ ((OAI.Analysis.PDE.Concentration.timeSpaceSplit (d + 1) 3 x).1,
      insertFourth (d + 1) (OAI.Analysis.PDE.Concentration.timeSpaceSplit (d + 1) 3 x).2)
  have hQ : ContDiff ℝ ∞ Q :=
    (contDiff_fst.comp (OAI.Analysis.PDE.Concentration.timeSpaceSplit (d + 1) 3).contDiff).prodMk
      ((insertFourth (d + 1)).contDiff.comp
        (contDiff_snd.comp (OAI.Analysis.PDE.Concentration.timeSpaceSplit (d + 1) 3).contDiff))
  let U := Q ⁻¹' (OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a ×ˢ univ)
  refine ⟨U, ((OAI.Analysis.PDE.Concentration.isOpen_physicalEnergyAnnulus a).prod isOpen_univ).preimage hQ.continuous,
    hg.comp hQ.contDiffOn (fun _ h ↦ h), ?_⟩
  intro x ht _hx
  change (OAI.Analysis.PDE.Concentration.timeSpaceSplit (d + 1) 3 x).1 ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a ∧ True
  refine ⟨?_, trivial⟩
  rw [OAI.Analysis.PDE.Concentration.fullPhysicalSplit_fullProjection, OAI.Analysis.PDE.Concentration.fullPhysicalSplit_snd_fst] at ht
  simpa only [OAI.Analysis.PDE.Concentration.timeSpaceSplit_fst, OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus, Set.mem_ofPred_eq] using ht

theorem full_latticePeriodic_of_fiber {d : ℕ}
    {ι : Type*} [Fintype ι] (b : Basis ι ℝ (Fin (d + 1) → ℝ))
    {f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → ℝ}
    (hf : ∀ z, OAI.Analysis.PDE.Dirichlet.LatticePeriodic (OAI.Analysis.PDE.Concentration.physicalSpatialSplit d) b
      (fun y ↦ f (OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z y))) :
    OAI.Analysis.PDE.Dirichlet.LatticePeriodic (OAI.Analysis.PDE.Concentration.fullPhysicalSplit d) b f := by
  intro x l
  let p := OAI.Analysis.PDE.Concentration.fullPhysicalSplit d x
  have heval (v : Fin (d + 1) → ℝ) :
      f ((OAI.Analysis.PDE.Concentration.fullPhysicalSplit d).symm (v,p.2.1,p.2.2)) =
        f (OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 p.2.1 ((OAI.Analysis.PDE.Concentration.physicalSpatialSplit d).symm (v,p.2.2))) := by
    rw [OAI.Analysis.PDE.Concentration.fullPhysicalSplit_symm, OAI.Analysis.PDE.Concentration.physicalSpatialSplit_symm]
  change f ((OAI.Analysis.PDE.Concentration.fullPhysicalSplit d).symm (p.1 + (l : _),p.2)) = _
  calc
    _ = f (OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 p.2.1
        ((OAI.Analysis.PDE.Concentration.physicalSpatialSplit d).symm (p.1 + (l : _),p.2.2))) := heval _
    _ = f (OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 p.2.1
        ((OAI.Analysis.PDE.Concentration.physicalSpatialSplit d).symm (p.1,p.2.2))) := by
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using
        hf p.2.1 ((OAI.Analysis.PDE.Concentration.physicalSpatialSplit d).symm (p.1,p.2.2)) l
    _ = f x := by
      rw [← heval]
      exact congrArg f ((OAI.Analysis.PDE.Concentration.fullPhysicalSplit d).symm_apply_apply x)

theorem unpadPacketFunction_periodic {d : ℕ}
    {ι : Type} [Fintype ι] (b : Basis ι ℝ (Fin (d + 1) → ℝ))
    {g : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4 → ℝ}
    (hp : ∀ z, OAI.Analysis.PDE.Dirichlet.LatticePeriodic (paddedPhysicalSplit d)
      (paddedLatticeBasis (m := d + 1) b) (fun x ↦ g (z,x))) :
    OAI.Analysis.PDE.Dirichlet.LatticePeriodic (OAI.Analysis.PDE.Concentration.fullPhysicalSplit d) b (unpadPacketFunction d g) := by
  apply full_latticePeriodic_of_fiber b
  intro z
  have hpz := hp z
  dsimp only [paddedPhysicalSplit] at hpz
  have hh : OAI.Analysis.PDE.Dirichlet.LatticePeriodic (OAI.Analysis.PDE.Concentration.physicalSpatialSplit d) b
      (fun y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3 ↦ g (z,insertFourth (d + 1) y)) :=
    latticePeriodic_insertFourth (m := d + 1) (P := Fin (d + 1) → ℝ)
      (V := Option (Fin d) → ℂ) (ι := ι) (W := ℝ)
      (e := OAI.Analysis.PDE.Concentration.physicalSpatialSplit d) (b := b)
      (f := fun x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4 ↦ g (z,x)) hpz
  simpa only [unpadPacketFunction_fiber] using hh

end OAI.Analysis.Fourier.WavePackets
