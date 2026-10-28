import OAI.RepresentationTheory.Weil.UnitarySplitting.HeisenbergStability
import OAI.RepresentationTheory.Weil.UnitarySplitting.DensityMeasure

/-! # Kernel -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.Kernel.Construction

noncomputable section

/-! The kernel of the actual oscillator extension consists exactly of
unit circle scalars, for all fields in the UnitarySplitting statement. -/

variable {F : Type} [NormedField F] [CompleteSpace F] [LocallyCompactSpace F] [CharZero F]
variable [MeasurableSpace F] [BorelSpace F] {d : ℕ}

omit [MeasurableSpace F] [BorelSpace F] in
theorem heisenberg_translation_apply (hF : ¬ DiscreteTopology F)
    (ψ : AddChar F ℂ) (hψ : Continuous (fun x : F => ψ x)) (hunit : ∀ t, ‖ψ t‖ = 1)
    (q : Local.FunctionsMetaplectic.Construction.Position F d) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) (x : Local.FunctionsMetaplectic.Construction.Position F d) :
    (HeisenbergStability.Construction.heisenbergOperator hF ψ hψ hunit (Sum.elim q 0) f).val x = f.val (x - q) := by
  change Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ (Sum.elim q 0) f.val x = _
  simp [Local.FunctionsMetaplectic.Construction.heisenbergFunction, Pi.sub_def]

theorem unitary_heisenberg_commutant_scalar (hF : ¬ DiscreteTopology F)
    (ψ : AddChar F ℂ) (hψ : Continuous (fun x : F => ψ x))
    (hunit : ∀ t, ‖ψ t‖ = 1) (hnontrivial : ∃ t, ψ t ≠ 1)
    (A : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d →ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat F d)
    (henergy : ∀ f, Local.FunctionsMetaplectic.Construction.l2Energy F d (A f) = Local.FunctionsMetaplectic.Construction.l2Energy F d f)
    (hA : ∀ v f, A (HeisenbergStability.Construction.heisenbergOperator hF ψ hψ hunit v f) =
      HeisenbergStability.Construction.heisenbergOperator hF ψ hψ hunit v (A f)) :
    ∃ z : Circle, ∀ f, A f = (z : ℂ) • f := by
  let : SecondCountableTopology F := TestSpaceAnalysis.Construction.localField_secondCountable F hF
  let M (p : Local.FunctionsMetaplectic.Construction.Position F d) : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d →ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat F d :=
    (HeisenbergStability.Construction.heisenbergOperator hF ψ hψ hunit (Sum.elim 0 p)).toLinearMap
  have hM (p : Local.FunctionsMetaplectic.Construction.Position F d) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) (x : Local.FunctionsMetaplectic.Construction.Position F d) :
      (M p f).val x = UltraMultiplier.Construction.modulationCharacter ψ p x * f.val x := by
    change Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ (Sum.elim 0 p) f.val x = _
    simp [Local.FunctionsMetaplectic.Construction.heisenbergFunction, UltraMultiplier.Construction.modulationCharacter, Local.FunctionsMetaplectic.Construction.dot]
  have hnorm (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) (x : Local.FunctionsMetaplectic.Construction.Position F d) : ‖(A f).val x‖ = ‖f.val x‖ :=
    DensityMeasure.Construction.energy_commutant_preserves_norm F ψ hψ hunit hnontrivial M hM A henergy
      (fun p g => hA (Sum.elim 0 p) g) f x
  have hzero (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) (x : Local.FunctionsMetaplectic.Construction.Position F d) (hx : f.val x = 0) :
      (A f).val x = 0 := by
    apply norm_eq_zero.mp
    rw [hnorm, hx, norm_zero]
  obtain ⟨u, hu⟩ := LocalTest.Construction.exists_test_nonzero F hF d
  obtain ⟨y, hy⟩ : ∃ y, u.val y ≠ 0 := by
    by_contra! h
    exact hu (Subtype.ext (funext h))
  let z : ℂ := (A u).val y / u.val y
  have hz : ‖z‖ = 1 := by
    rw [norm_div, hnorm, div_self (norm_ne_zero_iff.mpr hy)]
  refine ⟨⟨z, mem_sphere_zero_iff_norm.mpr hz⟩, fun f => ?_⟩
  apply Subtype.ext
  funext x
  let t := HeisenbergStability.Construction.heisenbergOperator hF ψ hψ hunit (Sum.elim (x - y) 0) u
  have ht : t.val x = u.val y := by
    rw [heisenberg_translation_apply]
    simp
  have hAt : (A t).val x = (A u).val y := by
    change (A (HeisenbergStability.Construction.heisenbergOperator hF ψ hψ hunit (Sum.elim (x - y) 0) u)).val x = _
    rw [hA, heisenberg_translation_apply]
    simp
  have hh := hzero (f - (f.val x / u.val y) • t) x (by
    change f.val x - (f.val x / u.val y) * t.val x = 0
    rw [ht, div_mul_cancel₀ _ hy, sub_self])
  rw [map_sub, map_smul] at hh
  change (A f).val x - (f.val x / u.val y) * (A t).val x = 0 at hh
  rw [hAt] at hh
  change (A f).val x = z * f.val x
  rw [sub_eq_zero] at hh
  rw [hh]
  dsimp [z]
  ring

variable {E : Type} [NormedField E] [Algebra F E] {m n : ℕ}
variable (σ : E ≃ₐ[F] E)
variable (H : Matrix (Fin m) (Fin m) E) (K : Matrix (Fin n) (Fin n) E)
variable (c : Oscillator.Construction.SymplecticFrame σ H K) (ψ : AddChar F ℂ)

theorem circleProjection_kernel (hF : ¬ DiscreteTopology F)
    (hψ : Continuous (fun x : F => ψ x)) (hunit : ∀ t, ‖ψ t‖ = 1)
    (hnontrivial : ∃ t, ψ t ≠ 1) (a : Oscillator.Construction.CircleExtension σ H K c ψ) :
    Oscillator.Construction.circleProjection σ H K c ψ a = 1 ↔
      ∃ z : Circle, Oscillator.Construction.circleScalar σ H K c ψ z = a := by
  constructor
  · intro ha
    have hA (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F (m * n)) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F (m * n)) :
        a.val.2 (HeisenbergStability.Construction.heisenbergOperator hF ψ hψ hunit v f) =
          HeisenbergStability.Construction.heisenbergOperator hF ψ hψ hunit v (a.val.2 f) := by
      have hgraph : Local.FunctionsMetaplectic.Construction.heisenbergGraph ψ (c.coordinates (c.coordinates.symm v)) f
          (HeisenbergStability.Construction.heisenbergOperator hF ψ hψ hunit v f) := by
        rw [c.coordinates.apply_symm_apply]
        rfl
      have hh := (a.property.2 (c.coordinates.symm v) f
        (HeisenbergStability.Construction.heisenbergOperator hF ψ hψ hunit v f)).mp hgraph
      have ha' : a.val.1 = 1 := ha
      change (a.val.2 (HeisenbergStability.Construction.heisenbergOperator hF ψ hψ hunit v f)).val =
        Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ (c.coordinates (a.val.1.val (c.coordinates.symm v)))
          (a.val.2 f).val at hh
      rw [ha'] at hh
      change (a.val.2 (HeisenbergStability.Construction.heisenbergOperator hF ψ hψ hunit v f)).val =
        Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ (c.coordinates (c.coordinates.symm v)) (a.val.2 f).val at hh
      rw [c.coordinates.apply_symm_apply] at hh
      exact Subtype.ext hh
    obtain ⟨z, hz⟩ := unitary_heisenberg_commutant_scalar hF ψ hψ hunit hnontrivial
      a.val.2.toLinearMap a.property.1 hA
    refine ⟨z, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · exact ha.symm
    · apply LinearEquiv.ext
      intro f
      exact (hz f).symm
  · rintro ⟨z, rfl⟩
    exact Oscillator.Construction.circleScalar_projects_to_one σ H K c ψ z

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.Kernel.Construction
