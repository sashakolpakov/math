import OAI.RepresentationTheory.Weil.UnitarySplitting.FourierPairing

/-! # Frame Transport -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.FrameTransport.Construction

noncomputable section

section

/-! Transport from standard symplectic coordinates into the actual
trace-tensor circle extension. -/

open scoped BigOperators

abbrev StandardSymplectic (F : Type) [NormedField F] (d : ℕ) :=
  DualPair.Construction.pairingIsometries (Oscillator.Construction.standardSymplecticPairing (F := F) d)

def rotationLinearEquiv {F : Type} [Field F] (d : ℕ) : Local.FunctionsMetaplectic.Construction.PhaseSpace F d ≃ₗ[F] Local.FunctionsMetaplectic.Construction.PhaseSpace F d where
  toFun := FourierCovariance.Construction.fourierPhaseRotation
  invFun v := Sum.elim (-FourierCovariance.Construction.phaseMomentum v) (FourierCovariance.Construction.phasePosition v)
  left_inv v := by funext i; cases i <;> simp [FourierCovariance.Construction.fourierPhaseRotation, FourierCovariance.Construction.phasePosition, FourierCovariance.Construction.phaseMomentum]
  right_inv v := by funext i; cases i <;> simp [FourierCovariance.Construction.fourierPhaseRotation, FourierCovariance.Construction.phasePosition, FourierCovariance.Construction.phaseMomentum]
  map_add' v w := by
    funext i
    cases i <;> simp [FourierCovariance.Construction.fourierPhaseRotation, FourierCovariance.Construction.phasePosition, FourierCovariance.Construction.phaseMomentum, add_comm]
  map_smul' a v := by funext i; cases i <;> simp [FourierCovariance.Construction.fourierPhaseRotation, FourierCovariance.Construction.phasePosition, FourierCovariance.Construction.phaseMomentum]

def rotationSymplectic {F : Type} [NormedField F] (d : ℕ) : StandardSymplectic F d :=
  ⟨rotationLinearEquiv d, by
    intro x y
    unfold Oscillator.Construction.standardSymplecticPairing
    apply Finset.sum_congr rfl
    intro i _
    change (-x (Sum.inl i)) * y (Sum.inr i) - x (Sum.inr i) * (-y (Sum.inl i)) = _
    ring⟩

variable {F E : Type} [NormedField F] [NormedField E] [Algebra F E] {m n : ℕ}
variable (σ : E ≃ₐ[F] E)
variable (H : Matrix (Fin m) (Fin m) E) (K : Matrix (Fin n) (Fin n) E)
variable (c : Oscillator.Construction.SymplecticFrame σ H K)

def frameSymplectic : StandardSymplectic F (m * n) →* Oscillator.Construction.TensorSymplectic σ H K where
  toFun g := ⟨(c.coordinates.trans g.val).trans c.coordinates.symm, by
    intro x y
    rw [← c.preserves, ← c.preserves x y]
    change Oscillator.Construction.standardSymplecticPairing (m * n)
      (c.coordinates (c.coordinates.symm (g.val (c.coordinates x))))
      (c.coordinates (c.coordinates.symm (g.val (c.coordinates y)))) = _
    rw [c.coordinates.apply_symm_apply, c.coordinates.apply_symm_apply]
    exact g.property _ _⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    exact c.coordinates.symm_apply_apply x
  map_mul' g h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change c.coordinates.symm (g.val (h.val (c.coordinates x))) =
      c.coordinates.symm (g.val (c.coordinates
        (c.coordinates.symm (h.val (c.coordinates x)))))
    rw [c.coordinates.apply_symm_apply]

theorem frameSymplectic_coordinates (g : StandardSymplectic F (m * n))
    (v : (Fin m × Fin n) → E) :
    c.coordinates ((frameSymplectic σ H K c g).val v) = g.val (c.coordinates v) :=
  c.coordinates.apply_symm_apply _

variable [CompleteSpace F] [LocallyCompactSpace F] [CharZero F]
variable [MeasurableSpace F] [BorelSpace F]
variable (hF : ¬ DiscreteTopology F) (ψ : AddChar F ℂ)
variable (hc : Continuous (fun t : F => ψ t)) (hunit : ∀ t, ‖ψ t‖ = 1)

def frameOscillatorLift (g : StandardSymplectic F (m * n))
    (U : Local.FunctionsMetaplectic.Construction.schwartzBruhat F (m * n) ≃ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat F (m * n))
    (henergy : ∀ f, Local.FunctionsMetaplectic.Construction.l2Energy F (m * n) (U f) = Local.FunctionsMetaplectic.Construction.l2Energy F (m * n) f)
    (hcov : ∀ v f, U (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hunit v f) =
      HeisenbergStability.Construction.heisenbergOperator hF ψ hc hunit (g.val v) (U f)) : Oscillator.Construction.CircleExtension σ H K c ψ := by
  refine ⟨(frameSymplectic σ H K c g, U), henergy, ?_⟩
  intro v f h
  rw [frameSymplectic_coordinates]
  change (h.val = Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ (c.coordinates v) f.val) ↔
    (U h).val = Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ (g.val (c.coordinates v)) (U f).val
  change h.val = (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hunit (c.coordinates v) f).val ↔
    (U h).val = (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hunit (g.val (c.coordinates v)) (U f)).val
  rw [← hcov]
  constructor
  · intro hh
    rw [Subtype.ext hh]
  · intro hh
    exact congrArg Subtype.val (U.injective (Subtype.ext hh))

theorem frameOscillatorLift_projection (g : StandardSymplectic F (m * n))
    (U : Local.FunctionsMetaplectic.Construction.schwartzBruhat F (m * n) ≃ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat F (m * n))
    (henergy : ∀ f, Local.FunctionsMetaplectic.Construction.l2Energy F (m * n) (U f) = Local.FunctionsMetaplectic.Construction.l2Energy F (m * n) f)
    (hcov : ∀ v f, U (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hunit v f) =
      HeisenbergStability.Construction.heisenbergOperator hF ψ hc hunit (g.val v) (U f)) :
    Oscillator.Construction.circleProjection σ H K c ψ (frameOscillatorLift σ H K c hF ψ hc hunit g U henergy hcov) =
      frameSymplectic σ H K c g := rfl

include hF hc hunit in
theorem exists_ultra_rotation_lift [IsUltrametricDist F]
    (hnontrivial : ∃ t, ψ t ≠ 1) :
    ∃ a : Oscillator.Construction.CircleExtension σ H K c ψ,
      Oscillator.Construction.circleProjection σ H K c ψ a = frameSymplectic σ H K c (rotationSymplectic (m * n)) := by
  let : SecondCountableTopology F := TestSpaceAnalysis.Construction.localField_secondCountable F hF
  obtain ⟨U, henergy, hcov⟩ := FourierPairing.Construction.exists_ultra_unitary_fourier hF ψ hc hunit hnontrivial
    (d := m * n)
  refine ⟨frameOscillatorLift σ H K c hF ψ hc hunit (rotationSymplectic (m * n)) U henergy ?_, rfl⟩
  intro v f
  apply Subtype.ext
  exact congrArg Subtype.val (hcov v f)

end

/-! Quadratic phase operators and their actual symplectic shear lifts. -/

open _root_.Matrix _root_.MeasureTheory
open scoped BigOperators

def shearFunction {F : Type} [Field F] {d : ℕ} (B : Matrix (Fin d) (Fin d) F)
    (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) : Local.FunctionsMetaplectic.Construction.PhaseSpace F d :=
  Sum.elim (FourierCovariance.Construction.phasePosition v) (B *ᵥ FourierCovariance.Construction.phasePosition v + FourierCovariance.Construction.phaseMomentum v)

def shearLinearEquiv {F : Type} [Field F] {d : ℕ} (B : Matrix (Fin d) (Fin d) F) :
    Local.FunctionsMetaplectic.Construction.PhaseSpace F d ≃ₗ[F] Local.FunctionsMetaplectic.Construction.PhaseSpace F d where
  toFun := shearFunction B
  invFun := shearFunction (-B)
  left_inv v := by
    funext i
    cases i <;> simp [shearFunction, FourierCovariance.Construction.phasePosition, FourierCovariance.Construction.phaseMomentum, Matrix.mulVec,
      dotProduct]
  right_inv v := by
    funext i
    cases i <;> simp [shearFunction, FourierCovariance.Construction.phasePosition, FourierCovariance.Construction.phaseMomentum, Matrix.mulVec,
      dotProduct]
  map_add' v w := by
    funext i
    cases i <;> simp [shearFunction, FourierCovariance.Construction.phasePosition, FourierCovariance.Construction.phaseMomentum, Matrix.mulVec,
      dotProduct, mul_add, Finset.sum_add_distrib, add_assoc, add_left_comm, add_comm]
  map_smul' a v := by
    funext i
    cases i <;> simp [shearFunction, FourierCovariance.Construction.phasePosition, FourierCovariance.Construction.phaseMomentum, Matrix.mulVec,
      dotProduct, Finset.mul_sum, mul_add, mul_left_comm]

theorem standardSymplecticPairing_dot {F : Type} [NormedField F] {d : ℕ}
    (v w : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) :
    Oscillator.Construction.standardSymplecticPairing d v w =
      Local.FunctionsMetaplectic.Construction.dot (FourierCovariance.Construction.phaseMomentum v) (FourierCovariance.Construction.phasePosition w) - Local.FunctionsMetaplectic.Construction.dot (FourierCovariance.Construction.phasePosition v) (FourierCovariance.Construction.phaseMomentum w) := by
  simp only [Oscillator.Construction.standardSymplecticPairing, Local.FunctionsMetaplectic.Construction.dot, FourierCovariance.Construction.phasePosition, FourierCovariance.Construction.phaseMomentum, Finset.sum_sub_distrib]

def shearSymplectic {F : Type} [NormedField F] {d : ℕ} (B : Local.FunctionsMetaplectic.Construction.SymmetricMatrix F d) :
    StandardSymplectic F d :=
  ⟨shearLinearEquiv B.val, by
    intro v w
    rw [standardSymplecticPairing_dot, standardSymplecticPairing_dot]
    change Local.FunctionsMetaplectic.Construction.dot (B.val *ᵥ FourierCovariance.Construction.phasePosition v + FourierCovariance.Construction.phaseMomentum v) (FourierCovariance.Construction.phasePosition w) -
      Local.FunctionsMetaplectic.Construction.dot (FourierCovariance.Construction.phasePosition v) (B.val *ᵥ FourierCovariance.Construction.phasePosition w + FourierCovariance.Construction.phaseMomentum w) = _
    have hcross : Local.FunctionsMetaplectic.Construction.dot (FourierCovariance.Construction.phasePosition v) (B.val *ᵥ FourierCovariance.Construction.phasePosition w) =
        Local.FunctionsMetaplectic.Construction.dot (B.val *ᵥ FourierCovariance.Construction.phasePosition v) (FourierCovariance.Construction.phasePosition w) := by
      change FourierCovariance.Construction.phasePosition v ⬝ᵥ B.val *ᵥ FourierCovariance.Construction.phasePosition w =
        (B.val *ᵥ FourierCovariance.Construction.phasePosition v) ⬝ᵥ FourierCovariance.Construction.phasePosition w
      rw [dotProduct_comm (B.val *ᵥ FourierCovariance.Construction.phasePosition v) (FourierCovariance.Construction.phasePosition w)]
      simpa only [B.property.eq] using
        Matrix.dotProduct_transpose_mulVec B.val (FourierCovariance.Construction.phasePosition v) (FourierCovariance.Construction.phasePosition w)
    simp only [Local.FunctionsMetaplectic.Construction.dot, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib] at *
    linear_combination -hcross⟩

theorem quadratic_dot {F : Type} [Field F] {d : ℕ}
    (B : Matrix (Fin d) (Fin d) F) (x : Local.FunctionsMetaplectic.Construction.Position F d) :
    Local.FunctionsMetaplectic.Construction.quadratic B x = Local.FunctionsMetaplectic.Construction.dot x (B *ᵥ x) / 2 := by
  simp [Local.FunctionsMetaplectic.Construction.quadratic, Local.FunctionsMetaplectic.Construction.dot, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

theorem quadratic_translate {F : Type} [Field F] [CharZero F] {d : ℕ}
    (B : Local.FunctionsMetaplectic.Construction.SymmetricMatrix F d) (x q : Local.FunctionsMetaplectic.Construction.Position F d) :
    Local.FunctionsMetaplectic.Construction.quadratic B.val x - Local.FunctionsMetaplectic.Construction.quadratic B.val (x - q) = Local.FunctionsMetaplectic.Construction.dot (B.val *ᵥ q) (x - (2 : F)⁻¹ • q) := by
  have hcross : Local.FunctionsMetaplectic.Construction.dot q (B.val *ᵥ x) = Local.FunctionsMetaplectic.Construction.dot x (B.val *ᵥ q) := by
    change q ⬝ᵥ B.val *ᵥ x = x ⬝ᵥ B.val *ᵥ q
    simpa only [B.property.eq] using Matrix.dotProduct_transpose_mulVec B.val q x
  rw [quadratic_dot, quadratic_dot]
  have hcomm : Local.FunctionsMetaplectic.Construction.dot (B.val *ᵥ q) (x - (2 : F)⁻¹ • q) =
      Local.FunctionsMetaplectic.Construction.dot (x - (2 : F)⁻¹ • q) (B.val *ᵥ q) := by
    unfold Local.FunctionsMetaplectic.Construction.dot
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hcomm]
  change (x ⬝ᵥ B.val *ᵥ x) / 2 - ((x - q) ⬝ᵥ B.val *ᵥ (x - q)) / 2 =
    (x - (2 : F)⁻¹ • q) ⬝ᵥ B.val *ᵥ q
  simp only [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct, smul_dotProduct, smul_eq_mul]
  change Local.FunctionsMetaplectic.Construction.dot x (B.val *ᵥ x) / 2 -
    (Local.FunctionsMetaplectic.Construction.dot x (B.val *ᵥ x) - Local.FunctionsMetaplectic.Construction.dot q (B.val *ᵥ x) -
      (Local.FunctionsMetaplectic.Construction.dot x (B.val *ᵥ q) - Local.FunctionsMetaplectic.Construction.dot q (B.val *ᵥ q))) / 2 = _
  rw [hcross]
  unfold Local.FunctionsMetaplectic.Construction.dot dotProduct
  ring

theorem quadratic_heisenberg {F : Type} [Field F] [CharZero F] {d : ℕ}
    (ψ : AddChar F ℂ) (B : Local.FunctionsMetaplectic.Construction.SymmetricMatrix F d) (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) (f : Local.FunctionsMetaplectic.Construction.Position F d → ℂ) :
    Local.FunctionsMetaplectic.Construction.quadraticOperator ψ B.val (Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v f) =
      Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ (shearFunction B.val v) (Local.FunctionsMetaplectic.Construction.quadraticOperator ψ B.val f) := by
  funext x
  rw [Local.FunctionsMetaplectic.Construction.quadraticOperator_apply, FourierCovariance.Construction.heisenbergFunction_dot, FourierCovariance.Construction.heisenbergFunction_dot,
    Local.FunctionsMetaplectic.Construction.quadraticOperator_apply, ← mul_assoc, ← mul_assoc, ← ψ.map_add_eq_mul, ← ψ.map_add_eq_mul]
  congr 2
  change Local.FunctionsMetaplectic.Construction.quadratic B.val x + Local.FunctionsMetaplectic.Construction.dot (FourierCovariance.Construction.phaseMomentum v) (x - (2 : F)⁻¹ • FourierCovariance.Construction.phasePosition v) =
    Local.FunctionsMetaplectic.Construction.dot (B.val *ᵥ FourierCovariance.Construction.phasePosition v + FourierCovariance.Construction.phaseMomentum v) (x - (2 : F)⁻¹ • FourierCovariance.Construction.phasePosition v) +
      Local.FunctionsMetaplectic.Construction.quadratic B.val (x - FourierCovariance.Construction.phasePosition v)
  have hh := quadratic_translate B x (FourierCovariance.Construction.phasePosition v)
  simp only [Local.FunctionsMetaplectic.Construction.dot, Pi.add_apply, add_mul, Finset.sum_add_distrib] at *
  linear_combination hh

section Ultra

variable {F : Type} [NormedField F] [IsUltrametricDist F] {d : ℕ}
variable (ψ : AddChar F ℂ) (hc : Continuous (fun t : F => ψ t))

include hc in
theorem ultra_quadratic_mem (B : Matrix (Fin d) (Fin d) F) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    Local.FunctionsMetaplectic.Construction.quadraticOperator ψ B f.val ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat F d := by
  obtain ⟨hf, hs⟩ := UltraMultiplier.Construction.schwartzBruhat_ultra_iff.mp f.property
  apply Local.FunctionsMetaplectic.Construction.compact_locallyConstant_mem
  · exact ((LocalTest.Construction.additiveCharacter_locallyConstant_ultra ψ hc).comp_continuous
      (by unfold Local.FunctionsMetaplectic.Construction.quadratic; fun_prop)).mul hf
  · exact hs.mul_left

def ultraQuadraticOperator (B : Matrix (Fin d) (Fin d) F) :
    Local.FunctionsMetaplectic.Construction.schwartzBruhat F d ≃ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat F d where
  toFun f := ⟨Local.FunctionsMetaplectic.Construction.quadraticOperator ψ B f.val, ultra_quadratic_mem ψ hc B f⟩
  invFun f := ⟨Local.FunctionsMetaplectic.Construction.quadraticOperator ψ (-B) f.val, ultra_quadratic_mem ψ hc (-B) f⟩
  left_inv f := by
    apply Subtype.ext
    funext x
    change ψ (Local.FunctionsMetaplectic.Construction.quadratic (-B) x) * (ψ (Local.FunctionsMetaplectic.Construction.quadratic B x) * f.val x) = f.val x
    rw [Local.FunctionsMetaplectic.Construction.quadratic_neg, ← mul_assoc, ← ψ.map_add_eq_mul]
    simp
  right_inv f := by
    apply Subtype.ext
    funext x
    change ψ (Local.FunctionsMetaplectic.Construction.quadratic B x) * (ψ (Local.FunctionsMetaplectic.Construction.quadratic (-B) x) * f.val x) = f.val x
    rw [Local.FunctionsMetaplectic.Construction.quadratic_neg, ← mul_assoc, ← ψ.map_add_eq_mul]
    simp
  map_add' f g := Subtype.ext ((Local.FunctionsMetaplectic.Construction.quadraticOperator ψ B).map_add f.val g.val)
  map_smul' a f := Subtype.ext ((Local.FunctionsMetaplectic.Construction.quadraticOperator ψ B).map_smul a f.val)

theorem ultraQuadraticOperator_unitary [LocallyCompactSpace F] [MeasurableSpace F] [BorelSpace F]
    (hunit : ∀ t, ‖ψ t‖ = 1) (B : Matrix (Fin d) (Fin d) F) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    Local.FunctionsMetaplectic.Construction.l2Energy F d (ultraQuadraticOperator ψ hc B f) = Local.FunctionsMetaplectic.Construction.l2Energy F d f := by
  unfold Local.FunctionsMetaplectic.Construction.l2Energy
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change ‖ψ (Local.FunctionsMetaplectic.Construction.quadratic B x) * f.val x‖ ^ 2 = ‖f.val x‖ ^ 2
    rw [norm_mul, hunit, one_mul]

end Ultra

variable {F E : Type} [NormedField F] [NormedField E] [Algebra F E]
variable [CompleteSpace F] [LocallyCompactSpace F] [CharZero F] [IsUltrametricDist F]
variable [MeasurableSpace F] [BorelSpace F] {m n : ℕ}
variable (σ : E ≃ₐ[F] E)
variable (H : Matrix (Fin m) (Fin m) E) (K : Matrix (Fin n) (Fin n) E)
variable (c : Oscillator.Construction.SymplecticFrame σ H K)
variable (hF : ¬ DiscreteTopology F) (ψ : AddChar F ℂ)
variable (hc : Continuous (fun t : F => ψ t)) (hunit : ∀ t, ‖ψ t‖ = 1)

def ultraShearLift (B : Local.FunctionsMetaplectic.Construction.SymmetricMatrix F (m * n)) : Oscillator.Construction.CircleExtension σ H K c ψ :=
  frameOscillatorLift σ H K c hF ψ hc hunit (shearSymplectic B)
    (ultraQuadraticOperator ψ hc B.val) (ultraQuadraticOperator_unitary ψ hc hunit B.val)
    (fun v f => Subtype.ext (quadratic_heisenberg ψ B v f.val))

theorem ultraShearLift_projection (B : Local.FunctionsMetaplectic.Construction.SymmetricMatrix F (m * n)) :
    Oscillator.Construction.circleProjection σ H K c ψ (ultraShearLift σ H K c hF ψ hc hunit B) =
      frameSymplectic σ H K c (shearSymplectic B) := rfl

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.FrameTransport.Construction
