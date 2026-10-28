import OAI.NumberTheory.ArithmeticGroups.Lattice
import OAI.NumberTheory.ArithmeticGroups.Period
import OAI.NumberTheory.ArithmeticGroups.Levels
import OAI.NumberTheory.ArithmeticGroups.Diagonal
import OAI.NumberTheory.ArithmeticGroups.Realize

/-! # Congruence Level Trace -/

namespace OAI.NumberTheory.ArithmeticGroups.CongruenceLevelTrace

noncomputable section

/-!
CongruenceLevel conditional on the explicit PrescribedSigns and RiemannProjectivity propositions. The general
integral-lattice and congruence-torsion arguments are proved here, so ArithmeticQuotient
and AuxiliaryApproximation are unnecessary inputs. Only declaration-equivalent elaboration
repairs are used; the committed statement specifications remain unchanged.
-/

open scoped Classical

variable {E : Type*} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E]

theorem reference_integral_trace_datum
    (b δ : E) (hb : b ≠ 0) (hδ : δ ≠ 0)
    (hbc : NumberField.IsCMField.complexConj E b = b)
    (hδc : NumberField.IsCMField.complexConj E δ = -δ) :
    ∃ m : ℕ, 0 < m ∧
      let Λ := Lattice.CongruenceLevel.standardLattice (E := E)
      let ψ := fun x y : Data.CongruenceLevel.VE E => (m : ℚ) * Trace.CongruenceLevel.rationalTrace b δ x y
      Data.CongruenceLevel.FullStableLattice Λ ∧
      (∀ x ∈ Λ, ∀ y ∈ Λ, ∃ n : ℤ, ψ x y = (n : ℚ)) ∧
      (∀ x, ψ x x = 0) ∧
      (∀ x, (∀ y, ψ x y = 0) → x = 0) ∧
      (∀ (a : E) (x y : Data.CongruenceLevel.VE E),
        ψ (a • x) y =
          ψ x (NumberField.IsCMField.complexConj E a • y)) ∧
      (∀ g : Data.CongruenceLevel.VE E ≃ₗ[E] Data.CongruenceLevel.VE E,
        (∀ x y, ψ (g x) (g y) = ψ x y) ↔
        (∀ x y, Data.CongruenceLevel.hermitian b (g x) (g y) = Data.CongruenceLevel.hermitian b x y)) := by
  obtain ⟨m, hm, hi, hib⟩ := Lattice.CongruenceLevel.exists_integral_trace_coefficients b δ
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  refine ⟨m, hm, Lattice.CongruenceLevel.standardLattice_full_stable, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    exact Lattice.CongruenceLevel.trace_integral_on_standardLattice b δ m hi hib x y hx hy
  · intro x
    simp only [Trace.CongruenceLevel.rationalTrace_alternating b δ hbc hδc, mul_zero]
  · intro x hx
    apply Trace.CongruenceLevel.rationalTrace_nondegenerate b δ hb hδ x
    intro y
    exact (mul_eq_zero.mp (hx y)).resolve_left hm0
  · intro a x y
    exact congrArg (fun q : ℚ => (m : ℚ) * q) (Trace.CongruenceLevel.trace_rosati b δ a x y)
  · intro g
    rw [← Trace.CongruenceLevel.trace_isometries_iff b δ hδ g]
    constructor
    · intro h x y
      exact mul_left_cancel₀ hm0 (h x y)
    · intro h x y
      exact congrArg (fun q : ℚ => (m : ℚ) * q) (h x y)

/-- CongruenceLevel with the complete prescribed reference datum, conditional only on
its PrescribedSigns period input and the RiemannProjectivity Riemann projectivity criterion. -/
theorem reference_polarized_abelian_moduli_datum
    {Place : Type*} [Fintype Place] [IsGalois ℚ E]
    (hPrescribedSigns : CongruenceLevelDatum.PrescribedSignsInput E Place) (hRiemannProjectivity : CongruenceLevelDatum.RiemannInput)
    (σ : Place → E →ₐ[ℚ] ℂ)
    (hσ : Function.Bijective
      (fun p : Place × Bool =>
        if p.2 then AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ p.1) else σ p.1))
    (μ : Place) (b : E)
    (hb : NumberField.IsCMField.complexConj E b = b)
    (hb_nonzero : b ≠ 0)
    (hμ : (σ μ b).re < 0)
    (hcompact : ∀ τ, τ ≠ μ → 0 < (σ τ b).re)
    (dref : Place → Bool) : CongruenceLevelDatum.ReferenceDatum σ μ b dref := by
  obtain ⟨δ₀, hδ₀, hδ₀c⟩ := Diagonal.CongruenceLevel.exists_nonzero_imaginary σ μ
  have hH := Diagonal.CongruenceLevel.diagonal_hermitian b hb
  have hneg : (Geometry.ComplexBall.PrescribedSignsB.localB σ (Matrix.diagonal ![1, 1, b]) μ ![0, 0, 1] ![0, 0, 1]).re < 0 := by
    simpa [Diagonal.CongruenceLevel.localB_diagonal] using hμ
  obtain ⟨a, ℱ, ha, hhol, hperiod, _, _, htrace⟩ :=
    hPrescribedSigns σ hσ μ δ₀ hδ₀ hδ₀c (Matrix.diagonal ![1, 1, b]) hH
      (Diagonal.CongruenceLevel.diagonal_positive_plane σ b μ) hneg
      (fun τ hτ => Or.inl (Diagonal.CongruenceLevel.diagonal_positive_definite σ b τ (hcompact τ hτ)))
      (fun _ => dref)
  let ξ := δ₀ * a 0
  have hξ : ξ ≠ 0 := mul_ne_zero hδ₀ (ha 0).1
  have hξc : NumberField.IsCMField.complexConj E ξ = -ξ := by
    dsimp only [ξ]
    rw [map_mul, hδ₀c, (ha 0).2.1]
    ring
  have hnξc : NumberField.IsCMField.complexConj E (-ξ) = -(-ξ) := by
    rw [map_neg, hξc]
  obtain ⟨m, hm, hΛ, hint, halt, hnd, hros, hiso⟩ :=
    reference_integral_trace_datum b (-ξ) hb_nonzero (neg_ne_zero.mpr hξ) hb hnξc
  let B := Geometry.ComplexBall.PrescribedSignsB.matrixB σ (Matrix.diagonal ![1, 1, b])
  let Ψ := Coordinates.CongruenceLevel.complexTrace B (fun τ => σ τ ξ)
  have hΨ (u v : Geometry.ComplexBall.PrescribedSignsB.Ambient Place) : Ψ u v =
      Geometry.ComplexBall.PrescribedSignsB.tracePairing (Geometry.ComplexBall.PrescribedSignsB.localB σ (Matrix.diagonal ![1, 1, b])) (fun τ => σ τ ξ) u v := by
    simp only [Ψ, B, Coordinates.CongruenceLevel.complexTrace_apply, Geometry.ComplexBall.PrescribedSignsB.matrixB_apply]
  have ht (τ : Place) : star (σ τ ξ) = -σ τ ξ := by
    have h : σ τ (NumberField.IsCMField.complexConj E ξ) = star (σ τ ξ) :=
      NumberField.IsCMField.complexEmbedding_complexConj E (σ τ).toRingHom ξ
    rw [hξc, map_neg] at h
    exact h.symm
  have hreal : ∀ u v, star (Ψ u v) =
      Ψ (Coordinates.CongruenceLevel.ambientConjugation Place u) (Coordinates.CongruenceLevel.ambientConjugation Place v) :=
    Coordinates.CongruenceLevel.complexTrace_real B (Geometry.ComplexBall.PrescribedSignsB.matrixB_hermitian σ _ hH) _ ht
  have hskew : ∀ u v, Ψ u v = -Ψ v u := Coordinates.CongruenceLevel.complexTrace_skew B _
  have htr (x y : Data.CongruenceLevel.VE E) : Ψ (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates σ x) (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates σ y) =
      (Trace.CongruenceLevel.rationalTrace b ξ x y : ℂ) := by
    rw [hΨ]
    have h := htrace 0 x y
    rw [Diagonal.CongruenceLevel.trace_matrix_diagonal] at h
    exact h
  unfold CongruenceLevelDatum.ReferenceDatum
  refine ⟨-ξ, m, Lattice.CongruenceLevel.standardLattice, ℱ 0, neg_ne_zero.mpr hξ, hnξc, hm,
    hΛ, hint, halt, hnd, hros, hiso, hhol 0, ?_, ?_⟩
  · intro z hz
    obtain ⟨hpres, hpos⟩ := hperiod 0 z hz
    refine ⟨hpres, ?_⟩
    have hp : Geometry.ComplexBall.PrescribedSignsB.PositivePeriod (3 * Fintype.card Place) (fun u v => Ψ u v)
        (Coordinates.CongruenceLevel.ambientConjugation Place) (ℱ 0 z) := by
      change Geometry.ComplexBall.PrescribedSignsB.PositivePeriod (3 * Fintype.card Place) (fun u v => Ψ u v) Geometry.ComplexBall.PrescribedSignsB.realConj (ℱ 0 z)
      simpa only [hΨ] using hpos
    exact Realize.CongruenceLevel.realize_positive_period hRiemannProjectivity σ hσ μ b ξ dref z Ψ (ℱ 0 z)
      hp hpres hreal hskew htr m hm hint
  · intro N₀ hN₀
    exact Levels.CongruenceLevel.arbitrarily_deep_principal_levels b _ hΛ N₀ hN₀

end

end OAI.NumberTheory.ArithmeticGroups.CongruenceLevelTrace
