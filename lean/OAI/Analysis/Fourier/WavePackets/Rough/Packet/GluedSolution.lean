import OAI.Analysis.Fourier.WavePackets.Rough.Packet.Unpadding
import OAI.Analysis.Fourier.WavePackets.Rough.Packet.GluedSlices

noncomputable section
open Set Filter Module
open scoped Topology ContDiff ComplexOrder
namespace OAI.Analysis.Fourier.WavePackets

open OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Concentration OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green OAI.LinearAlgebra.Moore

/-- Smooth parameter gluing preserves the actual physical equation.
The dummy fourth slot is removed by uniqueness, not by an assumed
independence property of the chosen extension. -/
theorem PaddedSolutionFamily.exists_physicalPacketSolution_of_gluing
    {n : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1))
    (h a : ℝ) (hh : 0 < h) (ha : 0 < a)
    (κ cR cI : ι → ℝ) (v : ι → Fin (n + 1) → ℝ)
    (hfreq : ∀ i j, ∃ l : ℤ, inner ℝ (OAI.Analysis.PDE.Concentration.packetSpatialFrequency (κ i) (v i))
      (R (EuclideanSpace.single (finSuccEquiv (n + 1) j) 1)) = (l : ℝ)*(2*Real.pi)/100)
    (lam : ℝ) (hlam : 0 < lam)
    (S : PaddedSolutionFamily (n + 1) a
      (paddedLatticeBasis (m := n + 2) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R))
      (packetPaddedBackground n a ha lam) (packetPaddedSource R h a ha κ cR cI v lam))
    (g : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 4 → ℝ)
    (hg : ContDiffOn ℝ ∞ g (OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a ×ˢ univ))
    (hp : ∀ z, OAI.Analysis.PDE.Dirichlet.LatticePeriodic (paddedPhysicalSplit (n + 1))
      (paddedLatticeBasis (m := n + 2) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R)) (fun x ↦ g (z,x)))
    (he : ∀ z ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a, ∀ x,
      paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) x ≤ 0 →
        g (z,x) = S.physicalValue (z,x)) :
    ∃ P : OAI.Analysis.PDE.Concentration.PhysicalPacketSolution R h a κ cR cI v lam,
      P.u = unpadPacketFunction (n + 1) g := by
  let u := unpadPacketFunction (n + 1) g
  have hu : OAI.Analysis.PDE.Concentration.PacketLocalSmooth (n + 1) a u := unpadPacketFunction_smooth hg
  have hprops := S.glued_descended_properties R h a hh ha κ cR cI v hfreq lam hlam g he
  have hnon : ∀ x ∈ OAI.Analysis.PDE.Green.physicalPropagationDomain (n + 1) a, u x ≤ 0 := by
    intro x hx
    obtain ⟨⟨z,y⟩,rfl⟩ := (OAI.Analysis.PDE.Concentration.timeSpaceSplit (n + 2) 3).symm.surjective x
    rw [OAI.Analysis.PDE.Concentration.timeSpaceSplit_symm] at hx ⊢
    have hz : z ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a := by
      simpa only [OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus, Set.mem_ofPred_eq, OAI.Analysis.PDE.Green.fullPhysicalProjection_fiber] using hx.1
    have hy : OAI.Analysis.PDE.Concentration.spatialDefiningFunction (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y < 0 := by
      simpa only [OAI.Analysis.PDE.Green.physicalFullDefining, OAI.Analysis.PDE.Green.fullPhysicalProjection_fiber,
        OAI.Analysis.PDE.Concentration.spatialDefiningFunction, Function.comp_apply] using hx.2
    simpa only [u, unpadPacketFunction_fiber] using (hprops z hz).2.1 y hy.le
  have hboundary : ∀ x,
      (a < ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection (n + 1) x).1‖ ∧
        ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection (n + 1) x).1‖ < 4) →
      OAI.Analysis.PDE.Green.physicalFullDefining (n + 1) a x = 0 → u x = 0 := by
    intro x ht hx
    obtain ⟨⟨z,y⟩,rfl⟩ := (OAI.Analysis.PDE.Concentration.timeSpaceSplit (n + 2) 3).symm.surjective x
    rw [OAI.Analysis.PDE.Concentration.timeSpaceSplit_symm] at ht hx ⊢
    have hz : z ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a := by
      simpa only [OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus, Set.mem_ofPred_eq, OAI.Analysis.PDE.Green.fullPhysicalProjection_fiber] using ht
    have hy : OAI.Analysis.PDE.Concentration.spatialDefiningFunction (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y = 0 := by
      simpa only [OAI.Analysis.PDE.Green.physicalFullDefining, OAI.Analysis.PDE.Green.fullPhysicalProjection_fiber,
        OAI.Analysis.PDE.Concentration.spatialDefiningFunction, Function.comp_apply] using hx
    simpa only [u, unpadPacketFunction_fiber] using (hprops z hz).1 y hy
  have hpositive : ∀ x ∈ OAI.Analysis.PDE.Green.physicalPropagationDomain (n + 1) a,
      (OAI.LinearAlgebra.Moore.complexify ((OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots
        (fun q ↦ lam * OAI.Analysis.PDE.Concentration.physicalBackground (n + 1) q + u q) x).submatrix Fin.succ Fin.succ)).PosDef := by
    intro x hx
    obtain ⟨⟨z,y⟩,rfl⟩ := (OAI.Analysis.PDE.Concentration.timeSpaceSplit (n + 2) 3).symm.surjective x
    rw [OAI.Analysis.PDE.Concentration.timeSpaceSplit_symm] at hx ⊢
    have hz : z ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a := by
      simpa only [OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus, Set.mem_ofPred_eq, OAI.Analysis.PDE.Green.fullPhysicalProjection_fiber] using hx.1
    have hy : OAI.Analysis.PDE.Concentration.spatialDefiningFunction (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y < 0 := by
      simpa only [OAI.Analysis.PDE.Green.physicalFullDefining, OAI.Analysis.PDE.Green.fullPhysicalProjection_fiber,
        OAI.Analysis.PDE.Concentration.spatialDefiningFunction, Function.comp_apply] using hx.2
    rw [← OAI.Analysis.PDE.Concentration.packetPotential_spatial_hessian_at lam z y
      ((hu.contDiffAt hx.1 hx.2.le).of_le (by simp))
      (OAI.Analysis.PDE.Concentration.physicalNullHeight_ne_zero_on_domain ha hx)]
    simpa only [u, unpadPacketFunction_fiber] using (hprops z hz).2.2.1 y hy
  have hequation : ∀ x ∈ OAI.Analysis.PDE.Green.physicalPropagationDomain (n + 1) a,
      OAI.LinearAlgebra.Moore.mooreDet (n + 2) ((OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots
        (fun q ↦ lam * OAI.Analysis.PDE.Concentration.physicalBackground (n + 1) q + u q) x).submatrix Fin.succ Fin.succ) =
          lam * (OAI.Analysis.PDE.Concentration.physicalLatticeCurrent R h a κ cR cI v x 0 0).re := by
    intro x hx
    obtain ⟨⟨z,y⟩,rfl⟩ := (OAI.Analysis.PDE.Concentration.timeSpaceSplit (n + 2) 3).symm.surjective x
    rw [OAI.Analysis.PDE.Concentration.timeSpaceSplit_symm] at hx ⊢
    have hz : z ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a := by
      simpa only [OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus, Set.mem_ofPred_eq, OAI.Analysis.PDE.Green.fullPhysicalProjection_fiber] using hx.1
    have hy : OAI.Analysis.PDE.Concentration.spatialDefiningFunction (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y < 0 := by
      simpa only [OAI.Analysis.PDE.Green.physicalFullDefining, OAI.Analysis.PDE.Green.fullPhysicalProjection_fiber,
        OAI.Analysis.PDE.Concentration.spatialDefiningFunction, Function.comp_apply] using hx.2
    rw [← OAI.Analysis.PDE.Concentration.packetPotential_spatial_hessian_at lam z y
      ((hu.contDiffAt hx.1 hx.2.le).of_le (by simp))
      (OAI.Analysis.PDE.Concentration.physicalNullHeight_ne_zero_on_domain ha hx)]
    simpa only [u, unpadPacketFunction_fiber] using (hprops z hz).2.2.2 y hy
  let P : OAI.Analysis.PDE.Concentration.PhysicalPacketSolution R h a κ cR cI v lam := {
    u := u
    smooth := hu
    periodic := OAI.Analysis.PDE.Concentration.cell_period_of_latticePeriodic_full (OAI.Analysis.PDE.Concentration.packetFullCoordinates n) R
      (unpadPacketFunction_periodic (OAI.Analysis.PDE.Concentration.packetSpatialBasis R) hp)
    nonpositive := hnon
    boundary := hboundary
    admissible := hpositive
    equation := hequation }
  exact ⟨P,rfl⟩

end OAI.Analysis.Fourier.WavePackets
