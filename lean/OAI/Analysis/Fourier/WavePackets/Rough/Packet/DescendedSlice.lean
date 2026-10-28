import OAI.Analysis.Fourier.WavePackets.Rough.Packet.SolutionComparison
import OAI.Analysis.Fourier.WavePackets.Packet.FixedSolution

noncomputable section
open Set Filter Module
open scoped Topology ContDiff ComplexOrder
namespace OAI.Analysis.Fourier.WavePackets

open OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Concentration OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green OAI.LinearAlgebra.Moore

/-- Every chosen physical fiber agrees with a genuine descended
three-slot solution. Uniqueness removes the arbitrary off-domain
extension of its defining function. -/
theorem PaddedSolutionFamily.exists_descended_slice
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
    (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) (hz : z ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a) :
    ∃ w : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 3 → ℝ,
      ContDiff ℝ ∞ w ∧
      (∀ y, OAI.Analysis.PDE.Concentration.spatialDefiningFunction (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y ≤ 0 →
        w y = S.physicalValue (z,insertFourth (n + 2) y)) ∧
      (∀ y, OAI.Analysis.PDE.Concentration.spatialDefiningFunction (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y = 0 → w y = 0) ∧
      (∀ y, OAI.Analysis.PDE.Concentration.spatialDefiningFunction (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y ≤ 0 → w y ≤ 0) ∧
      (∀ y, OAI.Analysis.PDE.Concentration.spatialDefiningFunction (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y < 0 →
        (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots
          (fun q ↦ lam * OAI.Analysis.PDE.Concentration.spatialBackgroundFunction (n + 1) (OAI.Analysis.PDE.Green.energyComplexTime z) q + w q) y)).PosDef) ∧
      (∀ y, OAI.Analysis.PDE.Concentration.spatialDefiningFunction (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y < 0 →
        OAI.LinearAlgebra.Moore.mooreDet (n + 2) (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots
          (fun q ↦ lam * OAI.Analysis.PDE.Concentration.spatialBackgroundFunction (n + 1) (OAI.Analysis.PDE.Green.energyComplexTime z) q + w q) y) =
          lam * (OAI.Analysis.PDE.Concentration.physicalLatticeCurrent R h a κ cR cI v
            (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y) 0 0).re) := by
  obtain ⟨D,hi,hc,hg,hB,hF⟩ := exists_packet_fixed_data_exact
    R h a hh ha κ cR cI v hfreq lam hlam z hz.1.le hz.2.le
  obtain ⟨S4⟩ := D.padFourth.nonempty_solution
  let w := S4.descend D
  have hci (x) : D.padFourth.defining x < 0 ↔ (S.data z).defining x < 0 := by
    change D.defining (dropFourth (n + 2) x) < 0 ↔ _
    rw [hi, (S.physical z hz).interior, paddedPhysicalDefining_eq]
  have hcc (x) : D.padFourth.defining x ≤ 0 ↔ (S.data z).defining x ≤ 0 := by
    change D.defining (dropFourth (n + 2) x) ≤ 0 ↔ _
    rw [hc, (S.physical z hz).closed, paddedPhysicalDefining_eq]
  have hcb : D.padFourth.background = (S.data z).background := by
    rw [(S.physical z hz).background]
    funext x
    change D.background (dropFourth (n + 2) x) = _
    rw [hB]
    rfl
  have hcf (x) (_hx : (S.data z).defining x < 0) :
      D.padFourth.density x = (S.data z).density x := by
    rw [(S.physical z hz).density]
    change D.density (dropFourth (n + 2) x) = _
    rw [hF]
    rfl
  have he := (S.solution z).eq_on_closed_of_same_data S4 hci hcc hcb hcf
  have hH (y) (hy : OAI.Analysis.PDE.Concentration.spatialDefiningFunction (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y ≤ 0) :
      OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots (fun q ↦ D.background q + w.u q) y =
      OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots
        (fun q ↦ lam * OAI.Analysis.PDE.Concentration.spatialBackgroundFunction (n + 1) (OAI.Analysis.PDE.Green.energyComplexTime z) q + w.u q) y := by
    apply OAI.Analysis.PDE.Dirichlet.quaternionHessian_congr_germ
    filter_upwards [(hg y hy).2.1] with q hq
    rw [hq]
  refine ⟨w.u,w.smooth,?_,?_,?_,?_,?_⟩
  · intro y hy
    apply he
    apply (hcc _).mp
    change D.defining (dropFourth (n + 2) (insertFourth (n + 2) y)) ≤ 0
    rw [dropFourth_insertFourth]
    exact (hc y).mpr hy
  · intro y hy
    exact w.boundary y ((hg y hy.le).1.eq_of_nhds.trans hy)
  · intro y hy
    apply S4.nonpositive
    change D.defining (dropFourth (n + 2) (insertFourth (n + 2) y)) ≤ 0
    rw [dropFourth_insertFourth]
    exact (hc y).mpr hy
  · intro y hy
    rw [← hH y hy.le]
    exact w.admissible y ((hi y).mpr hy)
  · intro y hy
    rw [← hH y hy.le, w.equation y ((hi y).mpr hy)]
    exact (hg y hy.le).2.2

end OAI.Analysis.Fourier.WavePackets
