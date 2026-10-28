import OAI.NumberTheory.ArithmeticGroups.CongruenceLevelDatum
import OAI.NumberTheory.ArithmeticGroups.EmbeddingLattice
import OAI.NumberTheory.ArithmeticGroups.Action

/-! # Realize -/

namespace OAI.NumberTheory.ArithmeticGroups.Realize.CongruenceLevel

noncomputable section

open scoped Classical

variable {E Place : Type*} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Fintype Place]

lemma rationalTrace_neg (b ξ : E) (x y : Data.CongruenceLevel.VE E) :
    Trace.CongruenceLevel.rationalTrace b (-ξ) x y = -Trace.CongruenceLevel.rationalTrace b ξ x y := by
  simp only [Trace.CongruenceLevel.rationalTrace, neg_mul, map_neg]

theorem realize_positive_period
    (hRiemannProjectivity : CongruenceLevelDatum.RiemannInput)
    (σ : Place → E →ₐ[ℚ] ℂ)
    (hσ : Function.Bijective
      (fun p : Place × Bool =>
        if p.2 then AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ p.1) else σ p.1))
    (μ : Place) (b ξ : E) (d : Place → Bool) (z : Geometry.ComplexBall.PrescribedSignsB.BallChart)
    (Ψ : LinearMap.BilinForm ℂ (Geometry.ComplexBall.PrescribedSignsB.Ambient Place))
    (P : Submodule ℂ (Geometry.ComplexBall.PrescribedSignsB.Ambient Place))
    (hP : Geometry.ComplexBall.PrescribedSignsB.PositivePeriod (3 * Fintype.card Place)
      (fun x y => Ψ x y) (Coordinates.CongruenceLevel.ambientConjugation Place) P)
    (hpres : ∀ u, u ∈ P ↔ Geometry.ComplexBall.PrescribedSignsB.Prescribed (Geometry.ComplexBall.PrescribedSignsB.localB σ (Matrix.diagonal ![1, 1, b])) μ d z u)
    (hreal : ∀ x y, star (Ψ x y) = Ψ (Coordinates.CongruenceLevel.ambientConjugation Place x) (Coordinates.CongruenceLevel.ambientConjugation Place y))
    (hskew : ∀ x y, Ψ x y = -Ψ y x)
    (htrace : ∀ x y : Data.CongruenceLevel.VE E, Ψ (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates σ x) (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates σ y) =
      (Trace.CongruenceLevel.rationalTrace b ξ x y : ℂ))
    (m : ℕ) (hm : 0 < m)
    (hint : ∀ x ∈ Lattice.CongruenceLevel.standardLattice (E := E), ∀ y ∈ Lattice.CongruenceLevel.standardLattice (E := E),
      ∃ n : ℤ, (m : ℚ) * Trace.CongruenceLevel.rationalTrace b (-ξ) x y = (n : ℚ)) :
    Data.CongruenceLevel.AnalyticPolarizedFiber σ (Lattice.CongruenceLevel.standardLattice (E := E))
      (fun x y => (m : ℚ) * Trace.CongruenceLevel.rationalTrace b (-ξ) x y) P := by
  let T := Fin (3 * Fintype.card Place) → ℂ
  obtain ⟨π, H₀, hker, hsurj, hsym, hpos, hriemann⟩ :=
    Period.CongruenceLevel.exists_positive_quotient (Coordinates.CongruenceLevel.ambientConjugation Place) (Coordinates.CongruenceLevel.ambientConjugation_involutive Place)
      Ψ P _ hP hreal hskew
  obtain ⟨hinj, Γ, hΓ, hdisc, hcomp⟩ := EmbeddingLattice.CongruenceLevel.period_projection_lattice σ hσ μ Ψ P hP π hker
  let H : T →ₗ⋆[ℂ] T →ₗ[ℂ] ℂ := (m : ℂ) • H₀
  have hHsym (u v : T) : H v u = star (H u v) := by
    change (m : ℂ) * H₀ v u = star ((m : ℂ) * H₀ u v)
    rw [hsym]
    simp only [star_mul, star_natCast]
    ring
  have hHpos (u : T) (hu : u ≠ 0) : 0 < (H u u).re := by
    change 0 < ((m : ℂ) * H₀ u u).re
    simpa [Complex.mul_re] using mul_pos (show (0 : ℝ) < m by exact_mod_cast hm) (hpos u hu)
  have hHt (x y : Data.CongruenceLevel.VE E) :
      (H (π (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates σ x)) (π (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates σ y))).im =
        (((m : ℚ) * Trace.CongruenceLevel.rationalTrace b (-ξ) x y : ℚ) : ℝ) := by
    have hfix (w : Data.CongruenceLevel.VE E) : Coordinates.CongruenceLevel.ambientConjugation Place (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates σ w) =
        Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates σ w := by
      rw [EmbeddingLattice.CongruenceLevel.embeddingCoordinates_real]
      exact Coordinates.CongruenceLevel.realCoordinates_fixed Place _
    have hp := hriemann (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates σ x) (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates σ y) (hfix x) (hfix y)
    rw [htrace] at hp
    calc
      (H (π (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates σ x)) (π (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates σ y))).im =
          (m : ℝ) * (H₀ (π (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates σ x)) (π (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates σ y))).im := by
        simp [H, LinearMap.smul_apply, smul_eq_mul, Complex.mul_im]
      _ = (m : ℝ) * -(Trace.CongruenceLevel.rationalTrace b ξ x y : ℝ) := by
        rw [hp]
        rfl
      _ = (((m : ℚ) * Trace.CongruenceLevel.rationalTrace b (-ξ) x y : ℚ) : ℝ) := by
        rw [rationalTrace_neg]
        push_cast
        rfl
  have hHint : ∀ u ∈ Γ, ∀ v ∈ Γ, ∃ n : ℤ, (H u v).im = (n : ℝ) := by
    intro u hu v hv
    obtain ⟨x, hx, rfl⟩ := (hΓ u).mp hu
    obtain ⟨y, hy, rfl⟩ := (hΓ v).mp hv
    obtain ⟨n, hn⟩ := hint x hx y hy
    refine ⟨n, ?_⟩
    rw [hHt, hn]
    norm_cast
  let : DiscreteTopology Γ := hdisc
  let : CompactSpace (T ⧸ Γ) := hcomp
  have hprojective : Data.CongruenceLevel.IsProjectiveComplexTorus T Γ :=
    (hRiemannProjectivity T Γ).mpr ⟨H, hHsym, hHpos, hHint⟩
  have hB : (fun τ x y => Geometry.ComplexBall.PrescribedSignsB.matrixB σ (Matrix.diagonal ![1, 1, b]) τ x y) =
      Geometry.ComplexBall.PrescribedSignsB.localB σ (Matrix.diagonal ![1, 1, b]) := by
    funext τ x y
    exact Geometry.ComplexBall.PrescribedSignsB.matrixB_apply σ _ τ x y
  obtain ⟨ρ, hρ⟩ := Action.CongruenceLevel.quotient_integer_action σ
    (Geometry.ComplexBall.PrescribedSignsB.matrixB σ (Matrix.diagonal ![1, 1, b])) μ d z P
    (by rw [hB]; exact hpres) π hker hsurj
  exact ⟨π, Γ, H, ρ, hker, hsurj, hinj, hΓ, hdisc, hcomp,
    hprojective, hHsym, hHpos, hHt, hρ⟩

end

end OAI.NumberTheory.ArithmeticGroups.Realize.CongruenceLevel
