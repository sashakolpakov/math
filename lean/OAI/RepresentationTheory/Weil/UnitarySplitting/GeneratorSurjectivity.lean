import OAI.RepresentationTheory.Weil.UnitarySplitting.UltraSurjectivity

/-! # Generator Surjectivity -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.GeneratorSurjectivity.Construction

noncomputable section

/-! A generator criterion for lifting all standard symplectic transformations. -/

theorem standard_generators_subgroup
    {F : Type} [NormedField F] [CharZero F] {d : ℕ}
    (S : Subgroup (FrameTransport.Construction.StandardSymplectic F d))
    (hrotation : FrameTransport.Construction.rotationSymplectic d ∈ S)
    (hshear : ∀ B : Local.FunctionsMetaplectic.Construction.SymmetricMatrix F d, FrameTransport.Construction.shearSymplectic B ∈ S) : S = ⊤ := by
  have ht (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) (a : F) : StandardTransvections.Construction.standardTransvection v a ∈ S := by
    have hpure (p : Local.FunctionsMetaplectic.Construction.Position F d) :
        StandardTransvections.Construction.standardTransvection (Sum.elim (0 : Local.FunctionsMetaplectic.Construction.Position F d) p) a ∈ S := by
      rw [StandardTransvections.Construction.standardTransvection_momentum]
      exact hshear _
    by_cases hq : FourierCovariance.Construction.phasePosition v = 0
    · have hv : v = Sum.elim (0 : Local.FunctionsMetaplectic.Construction.Position F d) (FourierCovariance.Construction.phaseMomentum v) := by
        funext i
        cases i with
        | inl j => exact congrFun hq j
        | inr j => rfl
      rw [hv]
      exact hpure _
    · obtain ⟨B, hB⟩ := StandardTransvections.Construction.shear_rotation_sends v hq
      let g := FrameTransport.Construction.shearSymplectic B * FrameTransport.Construction.rotationSymplectic d
      have hg : g ∈ S := S.mul_mem (hshear B) hrotation
      have hh := StandardTransvections.Construction.standardTransvection_conjugation g
        (Sum.elim (0 : Local.FunctionsMetaplectic.Construction.Position F d) (FourierCovariance.Construction.phasePosition v)) a
      rw [hB] at hh
      rw [← hh]
      exact S.mul_mem (S.mul_mem hg (hpure _)) (S.inv_mem hg)
  have hle : DualPair.Transvections.transvectionSubgroup (StandardTransvections.Construction.standardSymplecticBilinear F d)
      (StandardTransvections.Construction.standardSymplecticBilinear_alternating d) ≤ S := by
    apply (Subgroup.closure_le _).mpr
    rintro t ⟨⟨v, a⟩, rfl⟩
    exact ht v a
  apply top_unique
  intro g _
  exact hle (ComplementIsometry.Transvections.mem_transvectionSubgroup (StandardTransvections.Construction.standardSymplecticBilinear F d)
    (StandardTransvections.Construction.standardSymplecticBilinear_alternating d)
    (StandardTransvections.Construction.standardSymplecticBilinear_nondegenerate d) g)

theorem circleProjection_surjective_of_generators
    {F E : Type} [NormedField F] [NormedField E] [Algebra F E] [CharZero F]
    [LocallyCompactSpace F] [MeasurableSpace F] [BorelSpace F] {m n : ℕ}
    (σ : E ≃ₐ[F] E)
    (H : Matrix (Fin m) (Fin m) E) (K : Matrix (Fin n) (Fin n) E)
    (c : Oscillator.Construction.SymplecticFrame σ H K) (ψ : AddChar F ℂ)
    (hrotation : ∃ a : Oscillator.Construction.CircleExtension σ H K c ψ,
      Oscillator.Construction.circleProjection σ H K c ψ a = FrameTransport.Construction.frameSymplectic σ H K c (FrameTransport.Construction.rotationSymplectic (m * n)))
    (hshear : ∀ B : Local.FunctionsMetaplectic.Construction.SymmetricMatrix F (m * n), ∃ a : Oscillator.Construction.CircleExtension σ H K c ψ,
      Oscillator.Construction.circleProjection σ H K c ψ a = FrameTransport.Construction.frameSymplectic σ H K c (FrameTransport.Construction.shearSymplectic B)) :
    Function.Surjective (Oscillator.Construction.circleProjection σ H K c ψ) := by
  have htop := standard_generators_subgroup (UltraSurjectivity.Construction.liftableStandard σ H K c ψ)
    ((UltraSurjectivity.Construction.mem_liftableStandard σ H K c ψ _).mpr hrotation)
    (fun B => (UltraSurjectivity.Construction.mem_liftableStandard σ H K c ψ _).mpr (hshear B))
  intro h
  obtain ⟨g, hg⟩ := UltraSurjectivity.Construction.frameSymplectic_surjective σ H K c h
  have hmem : g ∈ UltraSurjectivity.Construction.liftableStandard σ H K c ψ := by rw [htop]; trivial
  obtain ⟨a, ha⟩ := (UltraSurjectivity.Construction.mem_liftableStandard σ H K c ψ g).mp hmem
  exact ⟨a, ha.trans hg⟩

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.GeneratorSurjectivity.Construction
