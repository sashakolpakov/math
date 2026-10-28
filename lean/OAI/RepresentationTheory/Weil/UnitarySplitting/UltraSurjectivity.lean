import OAI.RepresentationTheory.Weil.UnitarySplitting.StandardTransvections

/-! # Ultra Surjectivity -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.UltraSurjectivity.Construction

noncomputable section

/-! Surjectivity of the actual oscillator projection at ultrametric
places, from Fourier lifts, quadratic lifts, and transvection generation. -/

variable {F E : Type} [NormedField F] [NormedField E] [Algebra F E] {m n : ℕ}
variable (σ : E ≃ₐ[F] E)
variable (H : Matrix (Fin m) (Fin m) E) (K : Matrix (Fin n) (Fin n) E)
variable (c : Oscillator.Construction.SymplecticFrame σ H K)

theorem frameSymplectic_surjective : Function.Surjective (FrameTransport.Construction.frameSymplectic σ H K c) := by
  intro h
  let g : FrameTransport.Construction.StandardSymplectic F (m * n) :=
    ⟨(c.coordinates.symm.trans h.val).trans c.coordinates, by
      intro x y
      change Oscillator.Construction.standardSymplecticPairing (m * n)
        (c.coordinates (h.val (c.coordinates.symm x)))
        (c.coordinates (h.val (c.coordinates.symm y))) = _
      rw [c.preserves, h.property, ← c.preserves]
      rw [c.coordinates.apply_symm_apply, c.coordinates.apply_symm_apply]⟩
  refine ⟨g, ?_⟩
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change c.coordinates.symm (c.coordinates (h.val (c.coordinates.symm (c.coordinates x)))) = h.val x
  rw [c.coordinates.symm_apply_apply, c.coordinates.symm_apply_apply]

variable [LocallyCompactSpace F] [MeasurableSpace F] [BorelSpace F]
variable (ψ : AddChar F ℂ)

def liftableStandard : Subgroup (FrameTransport.Construction.StandardSymplectic F (m * n)) :=
  (Oscillator.Construction.circleProjection σ H K c ψ).toMonoidHom.range.comap (FrameTransport.Construction.frameSymplectic σ H K c)

theorem mem_liftableStandard (g : FrameTransport.Construction.StandardSymplectic F (m * n)) :
    g ∈ liftableStandard σ H K c ψ ↔
      ∃ a : Oscillator.Construction.CircleExtension σ H K c ψ, Oscillator.Construction.circleProjection σ H K c ψ a = FrameTransport.Construction.frameSymplectic σ H K c g :=
  Iff.rfl

variable [CompleteSpace F] [CharZero F] [IsUltrametricDist F]
variable (hF : ¬ DiscreteTopology F)
variable (hc : Continuous (fun t : F => ψ t)) (hunit : ∀ t, ‖ψ t‖ = 1)
variable (hnontrivial : ∃ t, ψ t ≠ 1)

include hF hc hunit hnontrivial in
theorem liftableStandard_rotation :
    FrameTransport.Construction.rotationSymplectic (m * n) ∈ liftableStandard σ H K c ψ :=
  (mem_liftableStandard σ H K c ψ _).mpr (FrameTransport.Construction.exists_ultra_rotation_lift σ H K c hF ψ hc hunit hnontrivial)

include hF hc hunit in
theorem liftableStandard_shear (B : Local.FunctionsMetaplectic.Construction.SymmetricMatrix F (m * n)) :
    FrameTransport.Construction.shearSymplectic B ∈ liftableStandard σ H K c ψ :=
  (mem_liftableStandard σ H K c ψ _).mpr
    ⟨FrameTransport.Construction.ultraShearLift σ H K c hF ψ hc hunit B, FrameTransport.Construction.ultraShearLift_projection σ H K c hF ψ hc hunit B⟩

include hF hc hunit hnontrivial in
theorem liftableStandard_transvection (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F (m * n)) (a : F) :
    StandardTransvections.Construction.standardTransvection v a ∈ liftableStandard σ H K c ψ := by
  have hpure (p : Local.FunctionsMetaplectic.Construction.Position F (m * n)) :
      StandardTransvections.Construction.standardTransvection (Sum.elim (0 : Local.FunctionsMetaplectic.Construction.Position F (m * n)) p) a ∈ liftableStandard σ H K c ψ := by
    rw [StandardTransvections.Construction.standardTransvection_momentum]
    exact liftableStandard_shear σ H K c ψ hF hc hunit _
  by_cases hq : FourierCovariance.Construction.phasePosition v = 0
  · have hv : v = Sum.elim (0 : Local.FunctionsMetaplectic.Construction.Position F (m * n)) (FourierCovariance.Construction.phaseMomentum v) := by
      funext i
      cases i with
      | inl j => exact congrFun hq j
      | inr j => rfl
    rw [hv]
    exact hpure _
  · obtain ⟨B, hB⟩ := StandardTransvections.Construction.shear_rotation_sends v hq
    let g := FrameTransport.Construction.shearSymplectic B * FrameTransport.Construction.rotationSymplectic (m * n)
    have hg : g ∈ liftableStandard σ H K c ψ :=
      (liftableStandard σ H K c ψ).mul_mem (liftableStandard_shear σ H K c ψ hF hc hunit B)
        (liftableStandard_rotation σ H K c ψ hF hc hunit hnontrivial)
    have hh := StandardTransvections.Construction.standardTransvection_conjugation g (Sum.elim (0 : Local.FunctionsMetaplectic.Construction.Position F (m * n)) (FourierCovariance.Construction.phasePosition v)) a
    rw [hB] at hh
    rw [← hh]
    exact (liftableStandard σ H K c ψ).mul_mem
      ((liftableStandard σ H K c ψ).mul_mem hg (hpure _))
      ((liftableStandard σ H K c ψ).inv_mem hg)

include hF hc hunit hnontrivial in
theorem circleProjection_surjective_ultra : Function.Surjective (Oscillator.Construction.circleProjection σ H K c ψ) := by
  have hle : DualPair.Transvections.transvectionSubgroup (StandardTransvections.Construction.standardSymplecticBilinear F (m * n))
      (StandardTransvections.Construction.standardSymplecticBilinear_alternating (m * n)) ≤ liftableStandard σ H K c ψ := by
    apply (Subgroup.closure_le _).mpr
    rintro t ⟨⟨v, a⟩, rfl⟩
    exact liftableStandard_transvection σ H K c ψ hF hc hunit hnontrivial v a
  intro h
  obtain ⟨g, hg⟩ := frameSymplectic_surjective σ H K c h
  have hmem : g ∈ liftableStandard σ H K c ψ := hle
    (ComplementIsometry.Transvections.mem_transvectionSubgroup (StandardTransvections.Construction.standardSymplecticBilinear F (m * n))
      (StandardTransvections.Construction.standardSymplecticBilinear_alternating (m * n))
      (StandardTransvections.Construction.standardSymplecticBilinear_nondegenerate (m * n)) g)
  obtain ⟨a, ha⟩ := (mem_liftableStandard σ H K c ψ g).mp hmem
  exact ⟨a, ha.trans hg⟩

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.UltraSurjectivity.Construction
