import OAI.Analysis.PDE.Concentration.Packet.EnergyBounds
import OAI.Analysis.PDE.Concentration.WaveIntegral

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Matrix _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet
open OAI.Analysis.PDE.Green OAI.LinearAlgebra.Moore
open scoped ContDiff Topology Matrix.Norms.Elementwise ComplexOrder MatrixOrder

theorem cylinderEnergyPoint_time (t r θ : ℝ) :
    cylinderEnergyEquiv (cylinderPoint t r θ) (0, 0) = t := by
  simp [cylinderPoint, cylinderRadial, cylinderAxis, EuclideanSpace.basisFun_apply]

theorem cylinderEnergyPoint_radius (t r θ : ℝ) (hr : 0 ≤ r) :
    ‖OAI.Analysis.PDE.Green.energyComplexTime (cylinderEnergyEquiv (cylinderPoint t r θ))‖ = r := by
  simp only [energyComplexTime_cylinderEnergyEquiv, cylinderComplexEquiv_point,
    Complex.norm_polarCoord_symm, abs_of_nonneg hr]

/-- The complete input/propagation/output concentration argument for a
normalized sector packet, conditional only on a genuine physical Dirichlet
solution and its quantitative boundary bounds. No intermediate energy or
recovery estimate is assumed. -/
theorem packet_restricted_bound_from_solution {n : ℕ} {K : Set (OAI.Analysis.Calculus.Current.SpatialSpace (n + 1))}
    (hK : IsCompact K) (hpos : ∀ η ∈ K, 0 < gaussianFrequencyK η)
    (hcap : ∀ η ∈ K, ‖gaussianVelocity η‖ ≤ 1 / 40) (A : ℝ) (hA : 0 ≤ A) :
    ∃ c C h₀ L₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < h₀ ∧ h₀ ≤ 1 ∧ 10000 ≤ L₀ ∧
      ∀ (R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1)),
      (∀ j, ‖R (EuclideanSpace.single j 1)‖ ≤ 1) →
      ∀ (h L : ℝ), 0 < h → h ≤ h₀ → L₀ ≤ L → 4 * (h * L) ≤ 1 →
      ∀ {ι : Type} [Fintype ι] (κ cR cI : ι → ℝ) (v : ι → Fin (n + 1) → ℝ)
      (m : ι → Option (Fin (n + 1)) → ℤ), Function.Injective m →
      (∀ k, 0 < κ k) →
      (∀ k i, inner ℝ (packetSpatialFrequency (κ k) (v k))
        (R (EuclideanSpace.single i 1)) = (m k i : ℝ) * (2 * Real.pi) / 100) →
      (∀ k, h • packetSpatialFrequency (κ k) (v k) ∈ K) →
      (∀ k, Real.sqrt L * ‖gaussianVelocity (h • packetSpatialFrequency (κ k) (v k))‖ ≤ A) →
      (∀ y, ‖packetBaseWave κ cR cI v 0 y‖ ≤ 1) →
      (∀ b < (1 : ℝ), ∃ y, b < ‖packetBaseWave κ cR cI v 0 y‖ ^ 2) →
      ∀ S : PhysicalPacketSolution R h (h * L) κ cR cI v (largeBackground (n + 1) h),
      ∀ ε G : ℝ, 0 ≤ ε → 0 ≤ G →
      (∀ x, (h * L < ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection (n + 1) x).1‖ ∧
          ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection (n + 1) x).1‖ < 4) → OAI.Analysis.PDE.Green.physicalFullDefining (n + 1) (h * L) x = 0 →
        ‖star (OAI.Analysis.PDE.Dirichlet.quaternionGradient OAI.Analysis.Calculus.Quaternion.threeSlots (OAI.Analysis.PDE.Green.physicalFullDefining (n + 1) (h * L)) x) ᵥ*
          physicalLatticeCurrent R h (h * L) κ cR cI v x‖ ≤ ε) →
      (∀ x, (h * L < ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection (n + 1) x).1‖ ∧
          ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection (n + 1) x).1‖ < 4) → OAI.Analysis.PDE.Green.physicalFullDefining (n + 1) (h * L) x = 0 →
        ‖OAI.Analysis.PDE.Dirichlet.quaternionGradient OAI.Analysis.Calculus.Quaternion.threeSlots S.u x‖ ≤ G) →
      c * h ^ 2 * L ^ (1 - (((n : ℝ) + 2) / ((n : ℝ) + 1)) *
        (gaussianDerivativeOrder (n + 1) : ℝ)) *
        (∫ t in (1 : ℝ)..2, ∫ y in physicalSpatialCell R,
          ‖packetBaseWave κ cR cI v (physicalNullTime (n + 1) t) y‖ ^
            (2 * (((n : ℝ) + 2) / ((n : ℝ) + 1)))) ≤
      C * (1 + |Real.log (2 * (h * L))|) ^ 3 *
        (h ^ 2 * L ^ ((n : ℝ) + 4 + (gaussianDerivativeOrder (n + 1) : ℝ) / (n + 1)) *
          (∫ y in physicalSpatialCell R, ‖packetBaseWave κ cR cI v 0 y‖ ^ 2) +
          packetPropagationError (packetFullCoordinates n) (packetSpatialCoordinates n) R ε G) := by
  obtain ⟨Ci, hCi, hin⟩ := packet_input_energy_bound hK hpos A hA
  obtain ⟨co, h₀, L₀, hco, hh₀, hh₀1, hL₀, hout⟩ := packet_output_energy_bound hK hpos hcap A hA
  obtain ⟨Cc, hCc, hcyl⟩ := exists_actual_packet_local_energy_cylinder_constant
  refine ⟨(2 * Real.pi) * co, Cc * max Ci 4, h₀, L₀,
    by positivity, mul_pos hCc (lt_of_lt_of_le (by norm_num) (le_max_right Ci 4)),
    hh₀, hh₀1, hL₀, ?_⟩
  intro R hR h L hh hsmall hL ha4 ι inst κ cR cI v m hm hκ hfreq hKmem hsector hnorm hnorm'
    S ε G hε hG hflux hgrad
  have hL1 : 1 ≤ L := by linarith
  have ha : 0 < h * L := mul_pos hh (lt_of_lt_of_le zero_lt_one hL1)
  let F := packetEnergy R h (h * L) κ cR cI v (largeBackground (n + 1) h) S.u
  let W : ℝ → ℝ := fun t => ∫ y in physicalSpatialCell R,
    ‖packetBaseWave κ cR cI v (physicalNullTime (n + 1) t) y‖ ^
      (2 * (((n : ℝ) + 2) / ((n : ℝ) + 1)))
  let δ := packetPropagationError (packetFullCoordinates n) (packetSpatialCoordinates n) R ε G
  let H := h ^ 2 * L ^ ((n : ℝ) + 4 + (gaussianDerivativeOrder (n + 1) : ℝ) / (n + 1)) *
    (∫ y in physicalSpatialCell R, ‖packetBaseWave κ cR cI v 0 y‖ ^ 2)
  have hδ : 0 ≤ δ := packetPropagationError_nonneg _ _ R hε hG
  have hH : 0 ≤ H := mul_nonneg (by positivity)
    (integral_nonneg (fun _ => sq_nonneg _))
  have hmem (t r φ : ℝ) (hlo : h * L < r) (hhi : r < 4) :
      cylinderEnergyEquiv (cylinderPoint t r φ) ∈ physicalEnergyAnnulus (h * L) := by
    change h * L < ‖OAI.Analysis.PDE.Green.energyComplexTime _‖ ∧ ‖OAI.Analysis.PDE.Green.energyComplexTime _‖ < 4
    rw [cylinderEnergyPoint_radius t r φ (ha.le.trans hlo.le)]
    exact ⟨hlo, hhi⟩
  have hi := hin R hR h L hh (hsmall.trans hh₀1) hL1 κ cR cI v m hm hκ hfreq hKmem
    hsector hnorm hnorm' (largeBackground (n + 1) h) (largeBackground_pos (n + 1) hh) S
    (cylinderEnergyEquiv (cylinderPoint 0 (4 * (h * L)) 0))
    (hmem _ _ _ (by linarith) (by linarith))
    (cylinderEnergyPoint_time _ _ _) (by rw [cylinderEnergyPoint_radius _ _ _ (by positivity)])
  have hi' : F (cylinderEnergyEquiv (cylinderPoint 0 (4 * (h * L)) 0)) ≤ Ci * H := by
    simpa only [F, H, mul_assoc] using hi
  have hFc : ContDiffOn ℝ ∞ F (physicalEnergyAnnulus (h * L)) :=
    contDiffOn_packetCombinedEnergy_local (packetFullCoordinates n) R h (h * L) hh ha κ cR cI v
      OAI.Analysis.Calculus.Quaternion.threeSlots (largeBackground (n + 1) h) S.smooth S.periodic
  have hKU : cylinderShell 1 2 (2 * (h * L)) (2 * (h * L)) ⊆ cylinderAnnulus (h * L) := by
    intro x hx
    exact ⟨by linarith [hx.2.1], by linarith [hx.2.2]⟩
  have hpoint (t : ℝ) (ht : t ∈ Icc (1 : ℝ) 2) (φ : ℝ) :
      (co * h ^ 2 * L ^ (1 - (((n : ℝ) + 2) / ((n : ℝ) + 1)) *
        (gaussianDerivativeOrder (n + 1) : ℝ))) * W t ≤
      (F ∘ cylinderEnergyEquiv) (cylinderPoint t (2 * (h * L)) φ) := by
    have hb := hout R hR h L hh hsmall hL κ cR cI v m hm hκ hfreq hKmem hsector hnorm S
      (cylinderEnergyEquiv (cylinderPoint t (2 * (h * L)) φ))
      (hmem _ _ _ (by linarith) (by linarith))
      (by rw [cylinderEnergyPoint_radius _ _ _ (by positivity)]; linarith)
    simpa only [cylinderEnergyPoint_time, F, W, Function.comp_apply] using hb
  have hlo := cylinder_integral_lower_of_time_bound (isOpen_cylinderAnnulus (h * L))
    (contDiffOn_comp_cylinderEnergyEquiv hFc) (by positivity : 0 ≤ 2 * (h * L)) hKU
    (continuous_packet_spatial_integral R κ cR cI v (fun i => (hκ i).le) (by positivity))
    _ hpoint
  have hcy := hcyl n (3 * n + 8) (3 * n + 5) ι (packetFullCoordinates n) (packetSpatialCoordinates n)
    R h (h * L) hh ha ha4 κ cR cI v
    (fun i j => ⟨m i (finSuccEquiv (n + 1) j), hfreq i (finSuccEquiv (n + 1) j)⟩)
    (largeBackground (n + 1) h) (largeBackground_pos (n + 1) hh) S.u S.smooth S.periodic
    S.nonpositive S.admissible S.equation ε G hε hG
    (fun x ht hr => ⟨S.boundary x ht hr, hflux x ht hr, hgrad x ht hr⟩) 0
  have hlog : 0 ≤ Cc * (1 + |Real.log (2 * (h * L))|) ^ 3 := by positivity
  have hupper : (∫ t in (1 : ℝ)..2, ∫ φ in (0 : ℝ)..(2 * Real.pi),
      F (cylinderEnergyEquiv (cylinderPoint t (2 * (h * L)) φ))) ≤
      (Cc * max Ci 4) * (1 + |Real.log (2 * (h * L))|) ^ 3 * (H + δ) := by
    have hinit : F (cylinderEnergyEquiv (cylinderPoint 0 (4 * (h * L)) 0)) + 4 * δ ≤
        Ci * H + 4 * δ := by linarith [hi']
    refine hcy.trans ((mul_le_mul_of_nonneg_left hinit hlog).trans ?_)
    have hb1 := mul_le_mul_of_nonneg_right (le_max_left Ci 4) hH
    have hb2 := mul_le_mul_of_nonneg_right (le_max_right Ci 4) hδ
    calc
      _ ≤ Cc * (1 + |Real.log (2 * (h * L))|) ^ 3 * (max Ci 4 * (H + δ)) :=
        mul_le_mul_of_nonneg_left (by nlinarith) hlog
      _ = _ := by ring
  have hall := hlo.trans hupper
  simpa only [W, H, δ, Function.comp_apply, mul_assoc] using hall

end OAI.Analysis.PDE.Concentration
