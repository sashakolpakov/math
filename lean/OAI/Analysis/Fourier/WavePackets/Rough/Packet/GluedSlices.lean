import OAI.Analysis.Fourier.WavePackets.Rough.Packet.DescendedSlice

noncomputable section
open Set Filter Module
open scoped Topology ContDiff ComplexOrder
namespace OAI.Analysis.Fourier.WavePackets

open OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Concentration OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green OAI.LinearAlgebra.Moore

theorem PaddedSolutionFamily.glued_descended_properties
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
    (he : ∀ z ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a, ∀ x,
      paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) x ≤ 0 →
        g (z,x) = S.physicalValue (z,x))
    (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) (hz : z ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a) :
    (∀ y, OAI.Analysis.PDE.Concentration.spatialDefiningFunction (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y = 0 →
      g (z,insertFourth (n + 2) y) = 0) ∧
    (∀ y, OAI.Analysis.PDE.Concentration.spatialDefiningFunction (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y ≤ 0 →
      g (z,insertFourth (n + 2) y) ≤ 0) ∧
    (∀ y, OAI.Analysis.PDE.Concentration.spatialDefiningFunction (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y < 0 →
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots
        (fun q ↦ lam * OAI.Analysis.PDE.Concentration.spatialBackgroundFunction (n + 1) (OAI.Analysis.PDE.Green.energyComplexTime z) q +
          g (z,insertFourth (n + 2) q)) y)).PosDef) ∧
    (∀ y, OAI.Analysis.PDE.Concentration.spatialDefiningFunction (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y < 0 →
      OAI.LinearAlgebra.Moore.mooreDet (n + 2) (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots
        (fun q ↦ lam * OAI.Analysis.PDE.Concentration.spatialBackgroundFunction (n + 1) (OAI.Analysis.PDE.Green.energyComplexTime z) q +
          g (z,insertFourth (n + 2) q)) y) =
        lam * (OAI.Analysis.PDE.Concentration.physicalLatticeCurrent R h a κ cR cI v
          (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y) 0 0).re) := by
  obtain ⟨w,hw,hwe,hwb,hwn,hwp,hwq⟩ :=
    S.exists_descended_slice R h a hh ha κ cR cI v hfreq lam hlam z hz
  have hge (y) (hy : OAI.Analysis.PDE.Concentration.spatialDefiningFunction (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y ≤ 0) :
      g (z,insertFourth (n + 2) y) = w y := by
    rw [he z hz _ (by simpa only [paddedPhysicalDefining_eq, dropFourth_insertFourth] using hy)]
    exact (hwe y hy).symm
  have hH (y) (hy : OAI.Analysis.PDE.Concentration.spatialDefiningFunction (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y < 0) :
      OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots
        (fun q ↦ lam * OAI.Analysis.PDE.Concentration.spatialBackgroundFunction (n + 1) (OAI.Analysis.PDE.Green.energyComplexTime z) q +
          g (z,insertFourth (n + 2) q)) y =
      OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots
        (fun q ↦ lam * OAI.Analysis.PDE.Concentration.spatialBackgroundFunction (n + 1) (OAI.Analysis.PDE.Green.energyComplexTime z) q + w q) y := by
    apply OAI.Analysis.PDE.Dirichlet.quaternionHessian_congr_germ
    have ho : IsOpen {q : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 3 |
        (S.data z).defining (insertFourth (n + 2) q) < 0} :=
      isOpen_lt ((S.data z).defining_smooth.continuous.comp
        (insertFourth (n + 2)).continuous) continuous_const
    have hmem : (S.data z).defining (insertFourth (n + 2) y) < 0 := by
      rw [(S.physical z hz).interior, paddedPhysicalDefining_eq, dropFourth_insertFourth]
      exact hy
    filter_upwards [ho.mem_nhds hmem] with q hq
    rw [hge q]
    have hh := (S.physical z hz).interior (insertFourth (n + 2) q) |>.mp hq
    simpa only [paddedPhysicalDefining_eq, dropFourth_insertFourth] using hh.le
  refine ⟨?_,?_,?_,?_⟩
  · intro y hy
    rw [hge y hy.le]
    exact hwb y hy
  · intro y hy
    rw [hge y hy]
    exact hwn y hy
  · intro y hy
    rw [hH y hy]
    exact hwp y hy
  · intro y hy
    rw [hH y hy]
    exact hwq y hy

end OAI.Analysis.Fourier.WavePackets
