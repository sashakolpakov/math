import OAI.Analysis.PDE.Concentration.ExtendedCurrentFacts
import OAI.Analysis.PDE.Concentration.Physical.LatticePropagation

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Filter Matrix _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet
open OAI.Analysis.PDE.Green OAI.LinearAlgebra.Moore
open scoped ContDiff Topology Matrix.Norms.Elementwise ComplexOrder MatrixOrder

/-- The actual packet energy satisfies weak propagation. Divergence,
Hermitian symmetry, positivity of the current/background, common boundary
kernel, and background annihilation are proved here from their concrete
formulas, rather than included among the hypotheses. -/
theorem packet_combined_energy_weak_bound {d m k : ℕ} {ι : Type*} [Fintype ι]
    (c : (Fin (d + 2) × Fin 3) ≃ Fin (m + 1))
    (b : (Fin (d + 1) × Fin 3) ≃ Fin (k + 1))
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (h a : ℝ) (hh : 0 < h) (ha : 0 < a)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (hfreq : ∀ i j, ∃ l : ℤ, inner ℝ (packetSpatialFrequency (κ i) (v i))
      (R (EuclideanSpace.single (finSuccEquiv d j) 1)) = (l : ℝ) * (2 * Real.pi) / 100)
    {lam : ℝ} (hlam : 0 < lam) {u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → ℝ}
    (hu : ContDiff ℝ 3 u)
    (hup : ∀ (j : Fin (d + 1)) x, u (x + physicalCellPeriod c R j) = u x)
    (hDpos : ∀ x ∈ OAI.Analysis.PDE.Green.physicalPropagationDomain d a,
      (OAI.LinearAlgebra.Moore.complexify ((OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots
        (fun y => lam * physicalBackground d y + u y) x).submatrix Fin.succ Fin.succ)).PosDef)
    (hequation : ∀ x ∈ OAI.Analysis.PDE.Green.physicalPropagationDomain d a,
      OAI.LinearAlgebra.Moore.mooreDet (d + 1) ((OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots
        (fun y => lam * physicalBackground d y + u y) x).submatrix Fin.succ Fin.succ) =
          lam * (physicalLatticeCurrent R h a κ cR cI v x 0 0).re)
    {ε G : ℝ} (hε : 0 ≤ ε) (hG : 0 ≤ G)
    (hboundary : ∀ x, (a < ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection d x).1‖ ∧
        ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection d x).1‖ < 4) → OAI.Analysis.PDE.Green.physicalFullDefining d a x = 0 →
      u x = 0 ∧
        ‖star (OAI.Analysis.PDE.Dirichlet.quaternionGradient OAI.Analysis.Calculus.Quaternion.threeSlots (OAI.Analysis.PDE.Green.physicalFullDefining d a) x) ᵥ*
          physicalLatticeCurrent R h a κ cR cI v x‖ ≤ ε ∧
        ‖OAI.Analysis.PDE.Dirichlet.quaternionGradient OAI.Analysis.Calculus.Quaternion.threeSlots u x‖ ≤ G)
    {η : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 → ℝ} (hη : ContDiff ℝ 3 η) (hηs : HasCompactSupport η)
    (hηpos : ∀ z, 0 ≤ η z)
    (hηann : ∀ z ∈ tsupport η, a < ‖OAI.Analysis.PDE.Green.energyComplexTime z‖ ∧ ‖OAI.Analysis.PDE.Green.energyComplexTime z‖ < 4) :
    (∫ z, Laplacian.laplacian η z * OAI.Analysis.PDE.Green.setFiberCombinedEnergy OAI.Analysis.Calculus.Quaternion.threeSlots lam
      (physicalLatticeEnergyCell R a) (physicalLatticeCurrent R h a κ cR cI v)
        (fun y => lam * physicalBackground d y) u z) ≤
      |(physicalCellLatticeMap c R).toLinearEquiv.toLinearMap.det| *
        ((d + 2 : ℕ) * ε * G * OAI.Analysis.PDE.Green.physicalCutoffConstant b * ∫ z, η z) := by
  let A := extendedPhysicalLatticeCurrent R h a ha κ cR cI v
  let B := fun y => lam * extendedPhysicalBackground d a ha y
  have hBgerm (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3)
      (ht : a ≤ ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection d x).1‖) (hr : OAI.Analysis.PDE.Green.physicalFullDefining d a x ≤ 0) :
      B =ᶠ[𝓝 x] (fun y => lam * physicalBackground d y) := by
    have hg := (extendedPhysical_fields_eq_near R h a ha κ cR cI v x ht hr).2
    filter_upwards [hg] with y hy
    exact congrArg (fun q : ℝ => lam * q) hy
  have hD (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) (hx : x ∈ OAI.Analysis.PDE.Green.physicalPropagationDomain d a) :
      OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots (fun y => B y + u y) x =
        OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots (fun y => lam * physicalBackground d y + u y) x := by
    apply OAI.Analysis.PDE.Dirichlet.quaternionHessian_congr_germ
    filter_upwards [hBgerm x hx.1.1.le hx.2.le] with y hy
    exact congrArg (fun q : ℝ => q + u y) hy
  have hB (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3)
      (ht : a ≤ ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection d x).1‖) (hr : OAI.Analysis.PDE.Green.physicalFullDefining d a x ≤ 0) :
      OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots B x =
        lam • OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots (physicalBackground d) x :=
    extendedPhysicalBackground_scaled_hessian a ha lam x ht hr
  have hAeq (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3)
      (ht : a ≤ ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection d x).1‖) (hr : OAI.Analysis.PDE.Green.physicalFullDefining d a x ≤ 0) :
      A x = physicalLatticeCurrent R h a κ cR cI v x :=
    (extendedPhysical_fields_eq_near R h a ha κ cR cI v x ht hr).1.eq_of_nhds
  have hdiv (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) (hx : x ∈ OAI.Analysis.PDE.Green.physicalPropagationDomain d a) (j) :
      OAI.Analysis.Calculus.Quaternion.strongDivergence OAI.Analysis.Calculus.Quaternion.threeSlots (fun p => fderiv ℝ A x (OAI.Analysis.PDE.Dirichlet.coordinateVector p)) j = 0 := by
    have hg := (extendedPhysical_fields_eq_near R h a ha κ cR cI v x hx.1.1.le hx.2.le).1
    change A =ᶠ[𝓝 x] physicalLatticeCurrent R h a κ cR cI v at hg
    rw [hg.fderiv_eq]
    exact physicalLatticeCurrent_strongDivergence_zero R h a hh κ cR cI v x
      (physicalNullHeight_ne_zero_on_domain ha hx) j
  have hcommon (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3)
      (ht : a < ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection d x).1‖ ∧ ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection d x).1‖ < 4)
      (hr : OAI.Analysis.PDE.Green.physicalFullDefining d a x = 0) :
      ∃ w : Fin (d + 2) → Quaternion ℝ, w ≠ 0 ∧
        OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots (OAI.Analysis.PDE.Green.physicalFullDefining d a) x *ᵥ w = 0 ∧
        OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots B x *ᵥ w = 0 ∧
        star (OAI.Analysis.PDE.Dirichlet.quaternionGradient OAI.Analysis.Calculus.Quaternion.threeSlots (OAI.Analysis.PDE.Green.physicalFullDefining d a) x) ⬝ᵥ w = 0 := by
    have hy : physicalNullHeight d x ≠ 0 := norm_pos_iff.mp
      (ha.trans_le (physicalNullHeight_on_closed_fiber d a ha x ht.1.le hr.le))
    obtain ⟨w, hw, hrw, hBw, hgw⟩ := physicalFullDefining_common_kernel d a ha.ne' x hy
    refine ⟨w, hw, hrw, ?_, hgw⟩
    rw [hB x ht.1.le hr.le, Matrix.smul_mulVec, hBw, smul_zero]
  have hApos (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) (hx : x ∈ OAI.Analysis.PDE.Green.physicalPropagationDomain d a) :
      (OAI.LinearAlgebra.Moore.complexify (A x)).PosSemidef := by
    rw [hAeq x hx.1.1.le hx.2.le]
    exact physicalLatticeCurrent_posSemidef R h a hh κ cR cI v x
      (physicalNullHeight_ne_zero_on_domain ha hx)
  have hBpos (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) (hx : x ∈ OAI.Analysis.PDE.Green.physicalPropagationDomain d a) :
      (OAI.LinearAlgebra.Moore.complexify ((OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots B x).submatrix Fin.succ Fin.succ)).PosSemidef := by
    have hp : (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots B x)).PosSemidef := by
      rw [hB x hx.1.1.le hx.2.le, OAI.LinearAlgebra.Moore.complexify_real_smul]
      exact (physicalBackground_hessian_posSemidef x
        (physicalNullHeight_ne_zero_on_domain ha hx)).smul hlam.le
    exact hp.submatrix (fun i : Fin (d + 1) × Fin 2 => (i.1.succ, i.2))
  have hann (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) (hx : x ∈ OAI.Analysis.PDE.Green.physicalPropagationDomain d a) :
      OAI.LinearAlgebra.Moore.realTrace (A x * OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots B x) = 0 := by
    rw [OAI.LinearAlgebra.Moore.realTrace_mul_comm, hAeq x hx.1.1.le hx.2.le, hB x hx.1.1.le hx.2.le,
      Matrix.smul_mul, physicalBackground_mul_latticeCurrent_zero R h a hh ha.ne' κ cR cI v x
        (physicalNullHeight_ne_zero_on_domain ha hx), smul_zero]
    simp [OAI.LinearAlgebra.Moore.realTrace]
  have hBdet (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) (hx : x ∈ OAI.Analysis.PDE.Green.physicalPropagationDomain d a) :
      OAI.LinearAlgebra.Moore.mooreDet (d + 2) (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots B x) = 0 := by
    rw [hB x hx.1.1.le hx.2.le, OAI.LinearAlgebra.Moore.mooreDet_smul,
      physicalBackground_mooreDet_zero d x (physicalNullHeight_ne_zero_on_domain ha hx), mul_zero]
  have hw := physical_lattice_combined_energy_weak_bound c b R OAI.Analysis.Calculus.Quaternion.threeSlots
    OAI.Analysis.Calculus.Quaternion.threeSlots_orthonormal a ha
    ((contDiff_extendedPhysicalLatticeCurrent R h a hh ha κ cR cI v).of_le (by simp))
    (extendedPhysicalLatticeCurrent_isHermitian R h a hh ha κ cR cI v)
    (fun j x => extendedPhysicalLatticeCurrent_cellPeriod c R h a ha κ cR cI v j
      (fun i => hfreq i j) x) hdiv
    ((contDiff_const.mul (contDiff_extendedPhysicalBackground d a ha)).of_le (by simp)) hu
    (fun j x => congrArg (fun q : ℝ => lam * q) (extendedPhysicalBackground_cellPeriod c R a ha j x))
    hup hcommon hlam hApos hBpos
    (fun x hx => by rw [hD x hx]; exact hDpos x hx)
    (fun x hx => by
      have hAx := hAeq x hx.1.1.le hx.2.le
      dsimp only [A] at hAx
      rw [hD x hx, hAx]
      exact hequation x hx)
    hann hBdet hε hG
    (fun x ht hr => by
      have hAx := hAeq x ht.1.le hr.le
      dsimp only [A] at hAx
      rw [hAx]
      exact hboundary x ht hr)
    hη hηs hηpos hηann
  convert hw using 1
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : Laplacian.laplacian η z = 0
  · simp only [hz, zero_mul]
  · rw [extendedPhysical_energy_eq R h a ha κ cR cI v OAI.Analysis.Calculus.Quaternion.threeSlots lam u z
      (hηann z (OAI.Analysis.PDE.Green.laplacian_nonzero_mem_tsupport hz)).1.le]

end OAI.Analysis.PDE.Concentration
