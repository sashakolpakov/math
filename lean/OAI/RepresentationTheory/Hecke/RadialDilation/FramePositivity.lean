import OAI.RepresentationTheory.Hecke.RadialDilation.RationalCoordinates
import OAI.RepresentationTheory.Hecke.RadialDilation.PositiveGraph

/-! # Frame Positivity -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization

noncomputable section

section

/-! Matrices of the actual PrescribedSigns frame in rational symplectic coordinates. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

variable {Place : Type*} [Fintype Place] [DecidableEq Place]
abbrev FrameIndex (Place : Type*) := Place × Fin 3

def flatFrame (B : Place → Geometry.ComplexBall.PrescribedSignsB.Bilin) (μ : Place) (d : Place → Bool) (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) :
    (FrameIndex Place → ℂ) →ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Ambient Place where
  toFun v := Geometry.ComplexBall.PrescribedSignsB.globalFrame B μ d z (fun τ i => v (τ, i))
  map_add' _ _ := map_add _ _ _
  map_smul' c v := by
    change Geometry.ComplexBall.PrescribedSignsB.globalFrame B μ d z (c • (fun τ i => v (τ, i))) =
      c • Geometry.ComplexBall.PrescribedSignsB.globalFrame B μ d z (fun τ i => v (τ, i))
    exact map_smul _ _ _

omit [DecidableEq Place] in
theorem flatFrame_scalar (B : Place → Geometry.ComplexBall.PrescribedSignsB.Bilin) (μ : Place) (d : Place → Bool)
    (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) (a : Place → ℂ) (v : FrameIndex Place → ℂ) :
    Complexification.Realization.pairedScalarEnd a (flatFrame B μ d z v) =
      flatFrame B μ d z (Archimedean.Realization.periodScalarMatrix μ d a *ᵥ v) := by
  simpa only [flatFrame, LinearMap.coe_mk, AddHom.coe_mk, Complexification.Realization.pairedScalarEnd,
    Archimedean.Realization.periodScalarMatrix, Matrix.mulVec_diagonal, Pi.mul_apply] using
    Archimedean.Realization.global_frame_scalar B μ d z a (fun τ i => v (τ, i))

def upperFrame
    (e : Geometry.ComplexBall.PrescribedSignsB.Ambient Place ≃ₗ[ℂ] (Sum (FrameIndex Place) (FrameIndex Place) → ℂ))
    (B : Place → Geometry.ComplexBall.PrescribedSignsB.Bilin) (μ : Place) (d : Place → Bool) (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) :
    Matrix (FrameIndex Place) (FrameIndex Place) ℂ :=
  LinearMap.toMatrix' ((LinearMap.funLeft ℂ ℂ Sum.inl).comp
    (e.toLinearMap.comp (flatFrame B μ d z)))

def lowerFrame
    (e : Geometry.ComplexBall.PrescribedSignsB.Ambient Place ≃ₗ[ℂ] (Sum (FrameIndex Place) (FrameIndex Place) → ℂ))
    (B : Place → Geometry.ComplexBall.PrescribedSignsB.Bilin) (μ : Place) (d : Place → Bool) (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) :
    Matrix (FrameIndex Place) (FrameIndex Place) ℂ :=
  LinearMap.toMatrix' ((LinearMap.funLeft ℂ ℂ Sum.inr).comp
    (e.toLinearMap.comp (flatFrame B μ d z)))

theorem upperFrame_mulVec
    (e : Geometry.ComplexBall.PrescribedSignsB.Ambient Place ≃ₗ[ℂ] (Sum (FrameIndex Place) (FrameIndex Place) → ℂ))
    (B : Place → Geometry.ComplexBall.PrescribedSignsB.Bilin) (μ : Place) (d : Place → Bool) (z : Geometry.ComplexBall.PrescribedSignsB.BallChart)
    (v : FrameIndex Place → ℂ) :
    upperFrame e B μ d z *ᵥ v = fun i => e (flatFrame B μ d z v) (Sum.inl i) :=
  LinearMap.toMatrix'_mulVec _ _

theorem lowerFrame_mulVec
    (e : Geometry.ComplexBall.PrescribedSignsB.Ambient Place ≃ₗ[ℂ] (Sum (FrameIndex Place) (FrameIndex Place) → ℂ))
    (B : Place → Geometry.ComplexBall.PrescribedSignsB.Bilin) (μ : Place) (d : Place → Bool) (z : Geometry.ComplexBall.PrescribedSignsB.BallChart)
    (v : FrameIndex Place → ℂ) :
    lowerFrame e B μ d z *ᵥ v = fun i => e (flatFrame B μ d z v) (Sum.inr i) :=
  LinearMap.toMatrix'_mulVec _ _

theorem frame_block_equations
    (e : Geometry.ComplexBall.PrescribedSignsB.Ambient Place ≃ₗ[ℂ] (Sum (FrameIndex Place) (FrameIndex Place) → ℂ))
    (B : Place → Geometry.ComplexBall.PrescribedSignsB.Bilin) (μ : Place) (d : Place → Bool) (z : Geometry.ComplexBall.PrescribedSignsB.BallChart)
    (a : Place → ℂ) (g : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks (FrameIndex Place) ℝ)
    (he : ∀ u, e (Complexification.Realization.pairedScalarEnd a u) =
      Matrix.fromBlocks g.complexify.A g.complexify.B g.complexify.C g.complexify.D *ᵥ e u) :
    g.complexify.A * upperFrame e B μ d z + g.complexify.B * lowerFrame e B μ d z =
        upperFrame e B μ d z * Archimedean.Realization.periodScalarMatrix μ d a ∧
    g.complexify.C * upperFrame e B μ d z + g.complexify.D * lowerFrame e B μ d z =
        lowerFrame e B μ d z * Archimedean.Realization.periodScalarMatrix μ d a := by
  have h (v : FrameIndex Place → ℂ) := he (flatFrame B μ d z v)
  simp only [flatFrame_scalar, Matrix.fromBlocks_mulVec] at h
  constructor <;> apply Matrix.ext_iff_mulVec.mpr <;> intro v
  · simpa only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, upperFrame_mulVec,
      lowerFrame_mulVec, Function.comp_def, Sum.elim_inl, Sum.elim_inr] using
      (congrArg (fun w => fun i => w (Sum.inl i)) (h v)).symm
  · simpa only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, upperFrame_mulVec,
      lowerFrame_mulVec, Function.comp_def, Sum.elim_inl, Sum.elim_inr] using
      (congrArg (fun w => fun i => w (Sum.inr i)) (h v)).symm

theorem rational_frame_block_equations
    (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
    (r : Eˣ)
    (hr : (r : E) * AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1)
    (σ : Place → E →ₐ[ℚ] ℂ) (hσ : Function.Bijective (Complexification.Realization.pairingEmbeddings σ))
    (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (FrameIndex Place) (FrameIndex Place) → ℚ))
    (B : Place → Geometry.ComplexBall.PrescribedSignsB.Bilin) (μ : Place) (d : Place → Bool) (z : Geometry.ComplexBall.PrescribedSignsB.BallChart)
    (γ : Theta.PoissonAutomorphyNormalizationData.Sp (FrameIndex Place) ℚ) (hγ : γ.val = RationalCoordinates.Realization.rationalScalarMatrix E e (r : E)) :
    let ec := RationalCoordinates.Realization.rationalCoordinates E σ hσ e
    let g := (Theta.PoissonAutomorphyNormalizationData.realBlocks γ).complexify
    let T := Archimedean.Realization.periodScalarMatrix μ d (fun τ => σ τ (r : E))
    g.A * upperFrame ec B μ d z + g.B * lowerFrame ec B μ d z =
        upperFrame ec B μ d z * T ∧
    g.C * upperFrame ec B μ d z + g.D * lowerFrame ec B μ d z =
        lowerFrame ec B μ d z * T := by
  apply frame_block_equations
  intro u
  rw [RationalCoordinates.Realization.rational_matrix_realizes_scalar E r hr σ hσ e]
  congr 1
  rw [← hγ]
  ext i j
  cases i <;> cases j <;>
    simp [Theta.PoissonAutomorphyNormalizationData.realBlocks, Theta.PoissonAutomorphyNormalizationData.blocks, Theta.PoissonAutomorphyNormalizationData.mapSp, AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.complexify,
      Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂]

end

/-! Transport of PrescribedSigns's positive Lagrangian to a Siegel period matrix. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

variable {ι : Type*} [Fintype ι]

def coordinatePairing {K : Type*} [CommRing K] (x y : Sum ι ι → K) : K :=
  ∑ i, (x (Sum.inl i) * y (Sum.inr i) - x (Sum.inr i) * y (Sum.inl i))

theorem coordinatePairing_star (x : Sum ι ι → ℂ) :
    coordinatePairing x (star x) =
      PositiveGraph.Realization.standardFramePairing (fun i => x (Sum.inl i)) (fun i => x (Sum.inr i)) := rfl

variable {Place : Type*} [Fintype Place] [DecidableEq Place]

omit [Fintype Place] [DecidableEq Place] in
theorem flatFrame_injective (B : Place → Geometry.ComplexBall.PrescribedSignsB.Bilin) (μ : Place) (d : Place → Bool)
    (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) : Function.Injective (flatFrame B μ d z) := by
  intro v w h
  have he := Geometry.ComplexBall.PrescribedSignsB.globalFrame_injective B μ d z h
  funext ⟨τ, i⟩
  exact congrFun (congrFun he τ) i

theorem frame_isotropic_matrix
    (e : Geometry.ComplexBall.PrescribedSignsB.Ambient Place ≃ₗ[ℂ] (Sum (FrameIndex Place) (FrameIndex Place) → ℂ))
    (B : Place → Geometry.ComplexBall.PrescribedSignsB.Bilin) (μ : Place) (d : Place → Bool) (z : Geometry.ComplexBall.PrescribedSignsB.BallChart)
    (hisotropic : ∀ v w, coordinatePairing (e (flatFrame B μ d z v))
      (e (flatFrame B μ d z w)) = 0) :
    (upperFrame e B μ d z).transpose * lowerFrame e B μ d z =
      (lowerFrame e B μ d z).transpose * upperFrame e B μ d z := by
  ext i j
  have h := hisotropic (Pi.single i 1) (Pi.single j 1)
  have hu v := upperFrame_mulVec e B μ d z v
  have hl v := lowerFrame_mulVec e B μ d z v
  unfold coordinatePairing at h
  simp_rw [← congrFun (hu (Pi.single i 1)), ← congrFun (hu (Pi.single j 1)),
    ← congrFun (hl (Pi.single i 1)), ← congrFun (hl (Pi.single j 1))] at h
  simp only [Matrix.mulVec_single_one] at h
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.col, Finset.sum_sub_distrib,
    sub_eq_zero] using h

/-- The only coordinate requirements are preservation of the symplectic form
and its real structure. Isotropy and positivity are supplied by PrescribedSigns. -/
theorem positivePeriod_frame_matrices
    (e : Geometry.ComplexBall.PrescribedSignsB.Ambient Place ≃ₗ[ℂ] (Sum (FrameIndex Place) (FrameIndex Place) → ℂ))
    (B : Place → Geometry.ComplexBall.PrescribedSignsB.Bilin) (μ : Place) (d : Place → Bool) (z : Geometry.ComplexBall.PrescribedSignsB.BallChart)
    (ψ : Geometry.ComplexBall.PrescribedSignsB.Ambient Place → Geometry.ComplexBall.PrescribedSignsB.Ambient Place → ℂ)
    (hpair : ∀ u v, coordinatePairing (e u) (e v) = ψ u v)
    (hreal : ∀ u, e (Geometry.ComplexBall.PrescribedSignsB.realConj u) = star (e u))
    (hp : Geometry.ComplexBall.PrescribedSignsB.PositivePeriod (3 * Fintype.card Place) ψ Geometry.ComplexBall.PrescribedSignsB.realConj
      (LinearMap.range (Geometry.ComplexBall.PrescribedSignsB.globalFrame B μ d z))) :
    (upperFrame e B μ d z).transpose * lowerFrame e B μ d z =
        (lowerFrame e B μ d z).transpose * upperFrame e B μ d z ∧
    ∀ v : FrameIndex Place → ℂ, v ≠ 0 →
      0 < (PositiveGraph.Realization.standardFramePairing (upperFrame e B μ d z *ᵥ v)
        (lowerFrame e B μ d z *ᵥ v)).im := by
  constructor
  · apply frame_isotropic_matrix
    intro v w
    rw [hpair]
    exact hp.2.2.1 _ ⟨_, rfl⟩ _ ⟨_, rfl⟩
  · intro v hv
    have hne : flatFrame B μ d z v ≠ 0 := by
      intro h
      apply hv
      exact flatFrame_injective B μ d z (by simpa using h)
    have hpos := (hp.2.2.2.1 _ ⟨_, rfl⟩ hne).2
    rw [← hpair, hreal, coordinatePairing_star] at hpos
    rw [upperFrame_mulVec, lowerFrame_mulVec]
    simpa [Complex.div_I, flatFrame] using hpos

end

end OAI.RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization
