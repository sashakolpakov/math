import OAI.RepresentationTheory.Weil.UnitarySplitting.ArchimedeanFourier
import OAI.RepresentationTheory.Weil.UnitarySplitting.GroupTopology

/-! # Circle Field Transport -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.CircleFieldTransport.Construction

noncomputable section

/-! Transport an actual continuous splitting through real field coordinates. -/

open _root_.MeasureTheory
open scoped NNReal

theorem circleExtension_tensor_covariance
    {F E : Type} [NormedField F] [NormedField E] [Algebra F E]
    [CompleteSpace F] [LocallyCompactSpace F] [CharZero F]
    [MeasurableSpace F] [BorelSpace F] {m n : ℕ}
    (σ : E ≃ₐ[F] E) (H : Matrix (Fin m) (Fin m) E) (K : Matrix (Fin n) (Fin n) E)
    (c : Oscillator.Construction.SymplecticFrame σ H K) (hF : ¬ DiscreteTopology F)
    (ψ : AddChar F ℂ) (hc : Continuous (fun t : F => ψ t)) (hu : ∀ t, ‖ψ t‖ = 1)
    (a : Oscillator.Construction.CircleExtension σ H K c ψ) (v : (Fin m × Fin n) → E) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F (m * n)) :
    a.val.2 (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu (c.coordinates v) f) =
      HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu (c.coordinates (a.val.1.val v)) (a.val.2 f) := by
  apply Subtype.ext
  exact (a.property.2 v f (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu (c.coordinates v) f)).mp rfl

theorem realField_splitting_transport
    {F E G : Type} [NormedField F] [NormedField E] [Algebra F E] [Algebra ℝ E]
    [CompleteSpace F] [LocallyCompactSpace F] [CharZero F]
    [MeasurableSpace F] [BorelSpace F] [Group G] [TopologicalSpace G] {m n : ℕ}
    (σ : E ≃ₐ[F] E) (σR : E ≃ₐ[ℝ] E)
    (H : Matrix (Fin m) (Fin m) E) (K : Matrix (Fin n) (Fin n) E)
    (c : Oscillator.Construction.SymplecticFrame σ H K) (cR : Oscillator.Construction.SymplecticFrame σR H K)
    (hF : ¬ DiscreteTopology F) (e : ℝ ≃+* F) (he : Continuous e) (hei : Continuous e.symm)
    (ψ : AddChar F ℂ) (hc : Continuous (fun t : F => ψ t)) (hu : ∀ t, ‖ψ t‖ = 1)
    (hcoords : ∀ v, cR.coordinates v = (FieldCoordinates.Construction.coordinateFieldEquiv (Fin (m * n) ⊕ Fin (m * n)) e he hei).symm (c.coordinates v))
    (δ : G →ₜ* Oscillator.Construction.TensorSymplectic σ H K)
    (sR : G →ₜ* Oscillator.Construction.CircleExtension σR H K cR (ψ.compAddMonoidHom e.toAddEquiv.toAddMonoidHom))
    (hproj : ∀ g v, (sR g).val.1.val v = (δ g).val v) :
    ∃ s : G →ₜ* Oscillator.Construction.CircleExtension σ H K c ψ, ∀ g, Oscillator.Construction.circleProjection σ H K c ψ (s g) = δ g := by
  let : SecondCountableTopology F := TestSpaceAnalysis.Construction.localField_secondCountable F hF
  let χ := ψ.compAddMonoidHom e.toAddEquiv.toAddMonoidHom
  let C := FieldCoordinates.Construction.crossFieldTestEquiv (FieldCoordinates.Construction.coordinateFieldEquiv (Fin (m * n)) e he hei)
  let U := fun g => (C.trans (sR g).val.2).trans C.symm
  have hcancel (g : G) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F (m * n)) : C (U g f) = (sR g).val.2 (C f) :=
    C.apply_symm_apply _
  have hC (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F (m * n)) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F (m * n)) :
      C (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu v f) =
        HeisenbergStability.Construction.heisenbergOperator RealFourierUnitary.Construction.real_nondiscrete χ (hc.comp he) (fun t => hu (e t))
          ((FieldCoordinates.Construction.coordinateFieldEquiv (Fin (m * n) ⊕ Fin (m * n)) e he hei).symm v) (C f) :=
    ArchimedeanFourier.Construction.realFieldTestEquiv_heisenberg hF e he hei ψ hc hu v f
  have hcov (g : G) (v : (Fin m × Fin n) → E) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F (m * n)) :
      U g (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu (c.coordinates v) f) =
        HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu (c.coordinates ((δ g).val v)) (U g f) := by
    apply C.injective
    rw [hcancel, hC, hC, hcancel, ← hcoords, ← hcoords]
    rw [circleExtension_tensor_covariance σR H K cR RealFourierUnitary.Construction.real_nondiscrete χ (hc.comp he)
      (fun t => hu (e t)), hproj]
  let s₀ : G →* Oscillator.Construction.CircleExtension σ H K c ψ :=
    { toFun := fun g => ⟨(δ g, U g),
        FieldCoordinates.Construction.crossFieldTestEquiv_transport_unitary _ (sR g).val.2 (sR g).property.1, by
          intro v f h
          change h.val = (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu (c.coordinates v) f).val ↔
            (U g h).val = (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu (c.coordinates ((δ g).val v)) (U g f)).val
          rw [← hcov]
          constructor
          · intro hh
            rw [Subtype.ext hh]
          · intro hh
            exact congrArg Subtype.val ((U g).injective (Subtype.ext hh))⟩
      map_one' := by
        apply Subtype.ext
        apply Prod.ext
        · exact map_one δ
        · apply LinearEquiv.ext
          intro f
          change C.symm ((sR 1).val.2 (C f)) = f
          rw [map_one]
          exact C.symm_apply_apply f
      map_mul' := by
        intro g h
        apply Subtype.ext
        apply Prod.ext
        · exact map_mul δ g h
        · apply LinearEquiv.ext
          intro f
          change C.symm ((sR (g * h)).val.2 (C f)) =
            C.symm ((sR g).val.2 (C (C.symm ((sR h).val.2 (C f)))))
          rw [C.apply_symm_apply, map_mul]
          rfl }
  have hcont : Continuous s₀ := by
    obtain ⟨r, hr⟩ := FieldCoordinates.Construction.crossFieldTestEquiv_energy_ratio (FieldCoordinates.Construction.coordinateFieldEquiv (Fin (m * n)) e he hei)
    have ho : Continuous (fun g => Oscillator.Construction.oscillatorObservations σR H K cR χ (sR g)) :=
      continuous_induced_dom.comp sR.continuous
    apply continuous_induced_rng.mpr
    apply Continuous.prodMk δ.continuous
    apply Continuous.prodMk
    · apply continuous_pi
      rintro ⟨f, k⟩
      change Continuous (fun g => Real.sqrt (Local.FunctionsMetaplectic.Construction.l2Energy F (m * n) (U g f - k)))
      have heq (g : G) : Real.sqrt (Local.FunctionsMetaplectic.Construction.l2Energy F (m * n) (U g f - k)) =
          Real.sqrt (r : ℝ) * Real.sqrt (Local.FunctionsMetaplectic.Construction.l2Energy ℝ (m * n) ((sR g).val.2 (C f) - C k)) := by
        rw [hr, map_sub, hcancel, Real.sqrt_mul r.coe_nonneg]
      simp_rw [heq]
      exact continuous_const.mul ((continuous_apply (C f, C k)).comp (continuous_fst.comp (continuous_snd.comp ho)))
    · apply continuous_pi
      rintro ⟨f, k⟩
      change Continuous (fun g => Real.sqrt (Local.FunctionsMetaplectic.Construction.l2Energy F (m * n) ((U g).symm f - k)))
      have hci (g : G) : C ((U g).symm f) = (sR g).val.2.symm (C f) := C.apply_symm_apply _
      have heq (g : G) : Real.sqrt (Local.FunctionsMetaplectic.Construction.l2Energy F (m * n) ((U g).symm f - k)) =
          Real.sqrt (r : ℝ) * Real.sqrt (Local.FunctionsMetaplectic.Construction.l2Energy ℝ (m * n) ((sR g).val.2.symm (C f) - C k)) := by
        rw [hr, map_sub, hci, Real.sqrt_mul r.coe_nonneg]
      simp_rw [heq]
      exact continuous_const.mul ((continuous_apply (C f, C k)).comp (continuous_snd.comp (continuous_snd.comp ho)))
  exact ⟨⟨s₀, hcont⟩, fun _ => rfl⟩

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.CircleFieldTransport.Construction
