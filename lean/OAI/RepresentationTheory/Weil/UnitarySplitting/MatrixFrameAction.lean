import OAI.RepresentationTheory.Weil.UnitarySplitting.MatrixUnitTopology
import OAI.RepresentationTheory.Weil.UnitarySplitting.FrameTransport
import OAI.RepresentationTheory.Weil.UnitarySplitting.Generic

/-! # Matrix Frame Action -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.MatrixFrameAction.Construction

noncomputable section

section

/-! Matrix unitary actions in prescribed continuous symplectic coordinates. -/

open _root_.Matrix

variable {F E I : Type} [NormedField F] [NormedField E] [Algebra F E]
variable [Fintype I] [DecidableEq I] {d : ℕ}

def matrixUnitContinuousLinearEquiv (u : (Matrix I I E)ˣ) : (I → E) ≃L[F] (I → E) where
  toLinearEquiv := DualPair.Construction.matrixLinearEquiv u
  continuous_toFun := (MatrixUnitTopology.Construction.matrixUnitContinuousAddEquiv u).continuous
  continuous_invFun := (MatrixUnitTopology.Construction.matrixUnitContinuousAddEquiv u).symm.continuous

def matrixFrameAction (σ : E ≃ₐ[F] E) (Q : Matrix I I E)
    (e : (I → E) ≃ₗ[F] Local.FunctionsMetaplectic.Construction.PhaseSpace F d)
    (he : ∀ x y, Oscillator.Construction.standardSymplecticPairing d (e x) (e y) = Algebra.trace F E (DualPair.Construction.sesquilinear σ Q x y) / 2) :
    DualPair.Construction.unitaryGroup σ Q →* FrameTransport.Construction.StandardSymplectic F d where
  toFun g := ⟨(e.symm.trans (DualPair.Construction.matrixLinearEquiv g.val)).trans e, by
    intro x y
    change Oscillator.Construction.standardSymplecticPairing d (e ((g.val : Matrix I I E) *ᵥ e.symm x))
      (e ((g.val : Matrix I I E) *ᵥ e.symm y)) = Oscillator.Construction.standardSymplecticPairing d x y
    rw [he, DualPair.Construction.unitary_preserves]
    have hh := he (e.symm x) (e.symm y)
    rw [e.apply_symm_apply, e.apply_symm_apply] at hh
    exact hh.symm⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change e ((1 : Matrix I I E) *ᵥ e.symm x) = x
    rw [Matrix.one_mulVec, e.apply_symm_apply]
  map_mul' g h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change e (((g.val : Matrix I I E) * (h.val : Matrix I I E)) *ᵥ e.symm x) =
      e ((g.val : Matrix I I E) *ᵥ e.symm (e ((h.val : Matrix I I E) *ᵥ e.symm x)))
    rw [e.symm_apply_apply, Matrix.mulVec_mulVec]

theorem matrixFrameAction_apply (σ : E ≃ₐ[F] E) (Q : Matrix I I E)
    (e : (I → E) ≃ₗ[F] Local.FunctionsMetaplectic.Construction.PhaseSpace F d)
    (he : ∀ x y, Oscillator.Construction.standardSymplecticPairing d (e x) (e y) = Algebra.trace F E (DualPair.Construction.sesquilinear σ Q x y) / 2)
    (g : DualPair.Construction.unitaryGroup σ Q) (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) :
    (matrixFrameAction σ Q e he g).val v = e ((g.val : Matrix I I E) *ᵥ e.symm v) := rfl

theorem matrixFrameAction_coordinates (σ : E ≃ₐ[F] E) (Q : Matrix I I E)
    (e : (I → E) ≃ₗ[F] Local.FunctionsMetaplectic.Construction.PhaseSpace F d)
    (he : ∀ x y, Oscillator.Construction.standardSymplecticPairing d (e x) (e y) = Algebra.trace F E (DualPair.Construction.sesquilinear σ Q x y) / 2)
    (g : DualPair.Construction.unitaryGroup σ Q) (x : I → E) :
    (matrixFrameAction σ Q e he g).val (e x) = e ((g.val : Matrix I I E) *ᵥ x) := by
  rw [matrixFrameAction_apply, e.symm_apply_apply]

theorem matrixFrameAction_continuous (σ : E ≃ₐ[F] E) (Q : Matrix I I E)
    (e : (I → E) ≃L[F] Local.FunctionsMetaplectic.Construction.PhaseSpace F d)
    (he : ∀ x y, Oscillator.Construction.standardSymplecticPairing d (e x) (e y) = Algebra.trace F E (DualPair.Construction.sesquilinear σ Q x y) / 2) :
    Continuous (matrixFrameAction σ Q e.toLinearEquiv he) := by
  apply continuous_induced_rng.mpr
  apply Continuous.prodMk
  · apply continuous_pi
    intro v
    change Continuous (fun g : DualPair.Construction.unitaryGroup σ Q => e ((g.val : Matrix I I E) *ᵥ e.symm v))
    apply e.continuous.comp
    fun_prop
  · apply continuous_pi
    intro v
    change Continuous (fun g : DualPair.Construction.unitaryGroup σ Q => e ((g.val⁻¹ : (Matrix I I E)ˣ) *ᵥ e.symm v))
    apply e.continuous.comp
    fun_prop

end

/-! Generic matrix differences define continuously varying invertible
Cayley coordinates in the actual symplectic frame. -/

open _root_.Matrix

variable {F E I : Type} [NormedField F] [NormedField E] [Algebra F E]
variable [Fintype I] [DecidableEq I] {d : ℕ}
variable (σ : E ≃ₐ[F] E) (Q : Matrix I I E) (e : (I → E) ≃L[F] Local.FunctionsMetaplectic.Construction.PhaseSpace F d)

def matrixFrameDifference (g : DualPair.Construction.unitaryGroup σ Q) (hg : g ∈ Generic.Construction.unitaryGenericDomain σ Q) :
    Local.FunctionsMetaplectic.Construction.PhaseSpace F d ≃L[F] Local.FunctionsMetaplectic.Construction.PhaseSpace F d :=
  (e.symm.trans (matrixUnitContinuousLinearEquiv
    (((g.val : Matrix I I E) - 1).nonsingInvUnit (isUnit_iff_ne_zero.mpr hg)))).trans e

theorem matrixFrameDifference_apply (g : DualPair.Construction.unitaryGroup σ Q) (hg : g ∈ Generic.Construction.unitaryGenericDomain σ Q)
    (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) : matrixFrameDifference σ Q e g hg v =
      e (((g.val : Matrix I I E) - 1) *ᵥ e.symm v) := rfl

theorem matrixFrameDifference_inverse_apply (g : DualPair.Construction.unitaryGroup σ Q) (hg : g ∈ Generic.Construction.unitaryGenericDomain σ Q)
    (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) : (matrixFrameDifference σ Q e g hg).symm v =
      e (((g.val : Matrix I I E) - 1)⁻¹ *ᵥ e.symm v) := rfl

theorem matrixFrameDifference_action
    (he : ∀ x y, Oscillator.Construction.standardSymplecticPairing d (e x) (e y) = Algebra.trace F E (DualPair.Construction.sesquilinear σ Q x y) / 2)
    (g : DualPair.Construction.unitaryGroup σ Q) (hg : g ∈ Generic.Construction.unitaryGenericDomain σ Q) (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) :
    matrixFrameDifference σ Q e g hg v = (matrixFrameAction σ Q e.toLinearEquiv he g).val v - v := by
  rw [matrixFrameDifference_apply, Matrix.sub_mulVec, Matrix.one_mulVec, map_sub,
    e.apply_symm_apply, matrixFrameAction_apply]
  rfl

theorem matrixFrameDifference_coordinates (g : DualPair.Construction.unitaryGroup σ Q) (hg : g ∈ Generic.Construction.unitaryGenericDomain σ Q)
    (x : I → E) : matrixFrameDifference σ Q e g hg (e x) = e (((g.val : Matrix I I E) - 1) *ᵥ x) := by
  rw [matrixFrameDifference_apply, e.symm_apply_apply]

theorem matrixFrameDifference_family_continuous
    {P : Type} [TopologicalSpace P] (g : P → DualPair.Construction.unitaryGroup σ Q) (hg : ∀ p, g p ∈ Generic.Construction.unitaryGenericDomain σ Q)
    (hc : Continuous g) :
    Continuous (fun z : P × Local.FunctionsMetaplectic.Construction.PhaseSpace F d => matrixFrameDifference σ Q e (g z.1) (hg z.1) z.2) ∧
      Continuous (fun z : P × Local.FunctionsMetaplectic.Construction.PhaseSpace F d => (matrixFrameDifference σ Q e (g z.1) (hg z.1)).symm z.2) := by
  have hA : Continuous (fun p : P => ((g p).val : Matrix I I E) - 1) := by fun_prop
  have hAi : Continuous (fun p : P => (((g p).val : Matrix I I E) - 1)⁻¹) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    have hi : ContinuousAt (fun A : Matrix I I E => A⁻¹) (((g p).val : Matrix I I E) - 1) := by
      apply continuousAt_matrix_inv
      have he : (Ring.inverse : E → E) = fun x => x⁻¹ := funext (fun x => Ring.inverse_eq_inv x)
      rw [he]
      exact continuousAt_inv₀ (hg p)
    exact hi.comp (f := fun t : P => ((g t).val : Matrix I I E) - 1) hA.continuousAt
  constructor
  · change Continuous (fun z : P × Local.FunctionsMetaplectic.Construction.PhaseSpace F d => e ((((g z.1).val : Matrix I I E) - 1) *ᵥ e.symm z.2))
    exact e.continuous.comp ((hA.comp continuous_fst).matrix_mulVec (e.symm.continuous.comp continuous_snd))
  · change Continuous (fun z : P × Local.FunctionsMetaplectic.Construction.PhaseSpace F d => e ((((g z.1).val : Matrix I I E) - 1)⁻¹ *ᵥ e.symm z.2))
    exact e.continuous.comp ((hAi.comp continuous_fst).matrix_mulVec (e.symm.continuous.comp continuous_snd))

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.MatrixFrameAction.Construction
