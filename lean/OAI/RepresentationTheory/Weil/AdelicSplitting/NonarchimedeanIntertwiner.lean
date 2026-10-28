import OAI.RepresentationTheory.Weil.AdelicSplitting.DeterminantMeasure
import OAI.RepresentationTheory.Weil.Local.Generators
import OAI.RepresentationTheory.Weil.AdelicSplitting.FourierTools

/-! # Nonarchimedean Intertwiner -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.NonarchimedeanIntertwiner.LocalAnalysis

noncomputable section

section

/- AdelicSplitting-owned copy of the checked LocalWeil analytic helper development.
Kept in a separate namespace so this proof commit has no dependency on
another task's uncommitted modules. -/

/-! Actual linear-substitution lifts to the Heisenberg oscillator extension. -/

open OAI.RepresentationTheory.Weil.Local.Generators.Construction

open _root_.Matrix _root_.MeasureTheory
open scoped BigOperators

def positionPart {k : Type} {n : ℕ} (v : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k n) : Weil.Local.FunctionsMetaplectic.Construction.Position k n :=
  fun i => v (Sum.inl i)

def momentumPart {k : Type} {n : ℕ} (v : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k n) : Weil.Local.FunctionsMetaplectic.Construction.Position k n :=
  fun i => v (Sum.inr i)

theorem heisenbergFunction_eq_dot {k : Type} [Field k] {n : ℕ}
    (ψ : AddChar k ℂ) (v : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k n) (f : Weil.Local.FunctionsMetaplectic.Construction.Position k n → ℂ) (x : Weil.Local.FunctionsMetaplectic.Construction.Position k n) :
    Weil.Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v f x =
      ψ (Weil.Local.FunctionsMetaplectic.Construction.dot (momentumPart v) (x - (2 : k)⁻¹ • positionPart v)) * f (x - positionPart v) := by
  unfold Weil.Local.FunctionsMetaplectic.Construction.heisenbergFunction Weil.Local.FunctionsMetaplectic.Construction.dot positionPart momentumPart
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
  rw [mul_comm (2 : k)⁻¹]

theorem positionPart_levi {k : Type} [Field k] {n : ℕ}
    (A : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k n) (v : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k n) :
    positionPart (Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (Weil.Local.Generators.Construction.leviSymplectic A) v) =
      (A : Matrix (Fin n) (Fin n) k) *ᵥ positionPart v := by
  funext i
  simp [positionPart, Weil.Local.FunctionsMetaplectic.Construction.symplecticAction, Weil.Local.Generators.Construction.leviSymplectic_matrix,
    Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks]

theorem momentumPart_levi {k : Type} [Field k] {n : ℕ}
    (A : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k n) (v : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k n) :
    momentumPart (Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (Weil.Local.Generators.Construction.leviSymplectic A) v) =
      (↑(A⁻¹) : Matrix (Fin n) (Fin n) k).transpose *ᵥ momentumPart v := by
  funext i
  simp [momentumPart, Weil.Local.FunctionsMetaplectic.Construction.symplecticAction, Weil.Local.Generators.Construction.leviSymplectic_matrix,
    Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks]

theorem substitutionOperator_heisenberg {k : Type} [Field k] {n : ℕ}
    (ψ : AddChar k ℂ) (A : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k n) (v : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k n)
    (f : Weil.Local.FunctionsMetaplectic.Construction.Position k n → ℂ) :
    Weil.Local.FunctionsMetaplectic.Construction.substitutionOperator A (Weil.Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v f) =
      Weil.Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ (Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (Weil.Local.Generators.Construction.leviSymplectic A) v) (Weil.Local.FunctionsMetaplectic.Construction.substitutionOperator A f) := by
  funext x
  rw [Weil.Local.FunctionsMetaplectic.Construction.substitutionOperator_apply, heisenbergFunction_eq_dot, heisenbergFunction_eq_dot,
    positionPart_levi, momentumPart_levi, Weil.Local.FunctionsMetaplectic.Construction.substitutionOperator_apply]
  have harg : (↑(A⁻¹) : Matrix (Fin n) (Fin n) k) *ᵥ
      (x - (↑A : Matrix (Fin n) (Fin n) k) *ᵥ positionPart v) =
      (↑(A⁻¹) : Matrix (Fin n) (Fin n) k) *ᵥ x - positionPart v := by
    simp only [Matrix.mulVec_sub, Matrix.mulVec_mulVec, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  rw [harg]
  congr 2
  symm
  rw [FourierTools.LocalAnalysis.dot_comm]
  change (x - (2 : k)⁻¹ • ((↑A : Matrix (Fin n) (Fin n) k) *ᵥ positionPart v)) ⬝ᵥ
      (↑(A⁻¹) : Matrix (Fin n) (Fin n) k).transpose *ᵥ momentumPart v = _
  rw [Matrix.dotProduct_transpose_mulVec]
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
    ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  rfl

theorem heisenbergFunction_smul {k : Type} [Field k] {n : ℕ}
    (ψ : AddChar k ℂ) (v : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k n) (f : Weil.Local.FunctionsMetaplectic.Construction.Position k n → ℂ) (c : ℂ) :
    Weil.Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v (c • f) = c • Weil.Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v f := by
  funext x
  simp only [Weil.Local.FunctionsMetaplectic.Construction.heisenbergFunction, Pi.smul_apply, smul_eq_mul]
  exact mul_left_comm _ _ _

variable {k : Type} [NormedField k] [LocallyCompactSpace k]
  [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {n : ℕ}

def normalizedRawSubstitution (A : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k n) :
    (Weil.Local.FunctionsMetaplectic.Construction.Position k n → ℂ) ≃ₗ[ℂ] (Weil.Local.FunctionsMetaplectic.Construction.Position k n → ℂ) :=
  (Weil.Local.FunctionsMetaplectic.Construction.substitutionOperator A).trans (LinearEquiv.smulOfUnit (LinearSubstitution.LocalAnalysis.coordinateScaleUnit (LinearSubstitution.LocalAnalysis.positionAddEquiv A)))

theorem normalizedRawSubstitution_val (A : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k n) (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    normalizedRawSubstitution A f.val = (LinearSubstitution.LocalAnalysis.normalizedCoordinate (LinearSubstitution.LocalAnalysis.positionAddEquiv A) f).val := rfl

theorem normalizedRawSubstitution_heisenberg
    (ψ : AddChar k ℂ) (A : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k n) (v : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k n) (f : Weil.Local.FunctionsMetaplectic.Construction.Position k n → ℂ) :
    normalizedRawSubstitution A (Weil.Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v f) =
      Weil.Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ (Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (Weil.Local.Generators.Construction.leviSymplectic A) v) (normalizedRawSubstitution A f) := by
  change (LinearSubstitution.LocalAnalysis.coordinateScale (LinearSubstitution.LocalAnalysis.positionAddEquiv A) : ℂ) • Weil.Local.FunctionsMetaplectic.Construction.substitutionOperator A (Weil.Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v f) =
    Weil.Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ (Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (Weil.Local.Generators.Construction.leviSymplectic A) v)
      ((LinearSubstitution.LocalAnalysis.coordinateScale (LinearSubstitution.LocalAnalysis.positionAddEquiv A) : ℂ) • Weil.Local.FunctionsMetaplectic.Construction.substitutionOperator A f)
  rw [heisenbergFunction_smul, substitutionOperator_heisenberg]

theorem normalizedCoordinate_intertwines
    (ψ : AddChar k ℂ) (A : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k n)
    (v : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k n) (f h : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    Weil.Local.FunctionsMetaplectic.Construction.heisenbergGraph ψ v f h ↔
      Weil.Local.FunctionsMetaplectic.Construction.heisenbergGraph ψ (Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (Weil.Local.Generators.Construction.leviSymplectic A) v)
        (LinearSubstitution.LocalAnalysis.normalizedCoordinate (LinearSubstitution.LocalAnalysis.positionAddEquiv A) f) (LinearSubstitution.LocalAnalysis.normalizedCoordinate (LinearSubstitution.LocalAnalysis.positionAddEquiv A) h) := by
  unfold Weil.Local.FunctionsMetaplectic.Construction.heisenbergGraph
  rw [← normalizedRawSubstitution_val, ← normalizedRawSubstitution_val,
    ← normalizedRawSubstitution_heisenberg]
  exact (normalizedRawSubstitution A).injective.eq_iff.symm

/-- This is an actual lift with the required positive determinant
normalization to the oscillator extension. Its bare-cover Weil-index
normalization is handled separately by the metaplectic argument. -/
def linearOscillator (ψ : AddChar k ℂ) (A : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k n) : Weil.Local.FunctionsMetaplectic.Construction.Oscillator k n ψ :=
  ⟨(Weil.Local.Generators.Construction.leviSymplectic A, LinearSubstitution.LocalAnalysis.normalizedCoordinate (LinearSubstitution.LocalAnalysis.positionAddEquiv A)),
    ⟨LinearSubstitution.LocalAnalysis.normalizedCoordinate_l2Energy (LinearSubstitution.LocalAnalysis.positionAddEquiv A), normalizedCoordinate_intertwines ψ A⟩⟩

theorem linearOscillator_apply (ψ : AddChar k ℂ) (A : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k n)
    (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) (x : Weil.Local.FunctionsMetaplectic.Construction.Position k n) :
    ((linearOscillator ψ A).val.2 f).val x =
      ((Real.sqrt (Weil.Local.FunctionsMetaplectic.Construction.localModulus k (Weil.Local.FunctionsMetaplectic.Construction.determinantUnit k A)))⁻¹ : ℂ) *
        f.val ((↑(A⁻¹) : Matrix (Fin n) (Fin n) k) *ᵥ x) :=
  DeterminantMeasure.LocalAnalysis.normalizedCoordinate_matrix_apply A f x

end

section

/-! Quadratic Heisenberg intertwiners on the concrete test-function space. -/

open OAI.RepresentationTheory.Weil.Local.Generators.Construction

open _root_.Matrix _root_.MeasureTheory
open scoped BigOperators

theorem quadratic_eq_dot {k : Type} [Field k] {n : ℕ}
    (B : Matrix (Fin n) (Fin n) k) (x : Weil.Local.FunctionsMetaplectic.Construction.Position k n) :
    Weil.Local.FunctionsMetaplectic.Construction.quadratic B x = Weil.Local.FunctionsMetaplectic.Construction.dot x (B *ᵥ x) / 2 := by
  simp [Weil.Local.FunctionsMetaplectic.Construction.quadratic, Weil.Local.FunctionsMetaplectic.Construction.dot, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

theorem quadratic_sub {k : Type} [Field k] [CharZero k] {n : ℕ}
    (B : Weil.Local.FunctionsMetaplectic.Construction.SymmetricMatrix k n) (x q : Weil.Local.FunctionsMetaplectic.Construction.Position k n) :
    Weil.Local.FunctionsMetaplectic.Construction.quadratic B.val x - Weil.Local.FunctionsMetaplectic.Construction.quadratic B.val (x - q) =
      Weil.Local.FunctionsMetaplectic.Construction.dot (B.val *ᵥ q) (x - (2 : k)⁻¹ • q) := by
  have hcross : Weil.Local.FunctionsMetaplectic.Construction.dot q (B.val *ᵥ x) = Weil.Local.FunctionsMetaplectic.Construction.dot x (B.val *ᵥ q) := by
    change q ⬝ᵥ B.val *ᵥ x = x ⬝ᵥ B.val *ᵥ q
    simpa only [B.property.eq] using Matrix.dotProduct_transpose_mulVec B.val q x
  rw [quadratic_eq_dot, quadratic_eq_dot, FourierTools.LocalAnalysis.dot_comm (B.val *ᵥ q)]
  change (x ⬝ᵥ B.val *ᵥ x) / 2 - ((x - q) ⬝ᵥ B.val *ᵥ (x - q)) / 2 =
    (x - (2 : k)⁻¹ • q) ⬝ᵥ B.val *ᵥ q
  simp only [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct,
    smul_dotProduct, smul_eq_mul]
  change Weil.Local.FunctionsMetaplectic.Construction.dot x (B.val *ᵥ x) / 2 -
    (Weil.Local.FunctionsMetaplectic.Construction.dot x (B.val *ᵥ x) - Weil.Local.FunctionsMetaplectic.Construction.dot q (B.val *ᵥ x) -
      (Weil.Local.FunctionsMetaplectic.Construction.dot x (B.val *ᵥ q) - Weil.Local.FunctionsMetaplectic.Construction.dot q (B.val *ᵥ q))) / 2 = _
  rw [hcross]
  unfold Weil.Local.FunctionsMetaplectic.Construction.dot dotProduct
  ring

theorem positionPart_quadratic {k : Type} [Field k] {n : ℕ}
    (B : Weil.Local.FunctionsMetaplectic.Construction.SymmetricMatrix k n) (v : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k n) :
    positionPart (Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (Weil.Local.Generators.Construction.quadraticSymplectic B) v) = positionPart v := by
  funext i
  simp [positionPart, Weil.Local.FunctionsMetaplectic.Construction.symplecticAction, Weil.Local.Generators.Construction.quadraticSymplectic_matrix,
    Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.one_apply]

theorem momentumPart_quadratic {k : Type} [Field k] {n : ℕ}
    (B : Weil.Local.FunctionsMetaplectic.Construction.SymmetricMatrix k n) (v : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k n) :
    momentumPart (Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (Weil.Local.Generators.Construction.quadraticSymplectic B) v) =
      B.val *ᵥ positionPart v + momentumPart v := by
  funext i
  simp [positionPart, momentumPart, Weil.Local.FunctionsMetaplectic.Construction.symplecticAction, Weil.Local.Generators.Construction.quadraticSymplectic_matrix,
    Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.one_apply]

theorem quadraticOperator_heisenberg {k : Type} [Field k] [CharZero k] {n : ℕ}
    (ψ : AddChar k ℂ) (B : Weil.Local.FunctionsMetaplectic.Construction.SymmetricMatrix k n) (v : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k n)
    (f : Weil.Local.FunctionsMetaplectic.Construction.Position k n → ℂ) :
    Weil.Local.FunctionsMetaplectic.Construction.quadraticOperator ψ B.val (Weil.Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v f) =
      Weil.Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ (Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (Weil.Local.Generators.Construction.quadraticSymplectic B) v)
        (Weil.Local.FunctionsMetaplectic.Construction.quadraticOperator ψ B.val f) := by
  funext x
  rw [Weil.Local.FunctionsMetaplectic.Construction.quadraticOperator_apply, heisenbergFunction_eq_dot, heisenbergFunction_eq_dot,
    positionPart_quadratic, momentumPart_quadratic, Weil.Local.FunctionsMetaplectic.Construction.quadraticOperator_apply,
    ← mul_assoc, ← mul_assoc, ← ψ.map_add_eq_mul, ← ψ.map_add_eq_mul]
  congr 2
  change Weil.Local.FunctionsMetaplectic.Construction.quadratic B.val x + Weil.Local.FunctionsMetaplectic.Construction.dot (momentumPart v) (x - (2 : k)⁻¹ • positionPart v) =
    Weil.Local.FunctionsMetaplectic.Construction.dot (B.val *ᵥ positionPart v + momentumPart v)
      (x - (2 : k)⁻¹ • positionPart v) + Weil.Local.FunctionsMetaplectic.Construction.quadratic B.val (x - positionPart v)
  have h := quadratic_sub B x (positionPart v)
  simp only [Weil.Local.FunctionsMetaplectic.Construction.dot, Pi.add_apply, add_mul, Finset.sum_add_distrib] at *
  linear_combination h

variable {k : Type} [NormedField k] {n : ℕ} (ψ : AddChar k ℂ)
    (hStable : ∀ (B : Matrix (Fin n) (Fin n) k) (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k n),
      Weil.Local.FunctionsMetaplectic.Construction.quadraticOperator ψ B f.val ∈ Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k n)

def testQuadratic (B : Matrix (Fin n) (Fin n) k) :
    Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k n ≃ₗ[ℂ] Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k n where
  toFun f := ⟨Weil.Local.FunctionsMetaplectic.Construction.quadraticOperator ψ B f.val, hStable B f⟩
  invFun f := ⟨Weil.Local.FunctionsMetaplectic.Construction.quadraticOperator ψ (-B) f.val, hStable (-B) f⟩
  left_inv f := by
    apply Subtype.ext
    funext x
    change ψ (Weil.Local.FunctionsMetaplectic.Construction.quadratic (-B) x) * (ψ (Weil.Local.FunctionsMetaplectic.Construction.quadratic B x) * f.val x) = f.val x
    rw [Weil.Local.FunctionsMetaplectic.Construction.quadratic_neg, ← mul_assoc, ← ψ.map_add_eq_mul]
    simp
  right_inv f := by
    apply Subtype.ext
    funext x
    change ψ (Weil.Local.FunctionsMetaplectic.Construction.quadratic B x) * (ψ (Weil.Local.FunctionsMetaplectic.Construction.quadratic (-B) x) * f.val x) = f.val x
    rw [Weil.Local.FunctionsMetaplectic.Construction.quadratic_neg, ← mul_assoc, ← ψ.map_add_eq_mul]
    simp
  map_add' f g := Subtype.ext ((Weil.Local.FunctionsMetaplectic.Construction.quadraticOperator ψ B).map_add f.val g.val)
  map_smul' c f := Subtype.ext ((Weil.Local.FunctionsMetaplectic.Construction.quadraticOperator ψ B).map_smul c f.val)

theorem testQuadratic_val (B : Matrix (Fin n) (Fin n) k) (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    (testQuadratic ψ hStable B f).val = Weil.Local.FunctionsMetaplectic.Construction.quadraticOperator ψ B f.val := rfl

theorem testQuadratic_intertwines [CharZero k] (B : Weil.Local.FunctionsMetaplectic.Construction.SymmetricMatrix k n)
    (v : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k n) (f h : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    Weil.Local.FunctionsMetaplectic.Construction.heisenbergGraph ψ v f h ↔
      Weil.Local.FunctionsMetaplectic.Construction.heisenbergGraph ψ (Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (Weil.Local.Generators.Construction.quadraticSymplectic B) v)
        (testQuadratic ψ hStable B.val f) (testQuadratic ψ hStable B.val h) := by
  unfold Weil.Local.FunctionsMetaplectic.Construction.heisenbergGraph
  rw [testQuadratic_val, testQuadratic_val, ← quadraticOperator_heisenberg]
  exact (Weil.Local.FunctionsMetaplectic.Construction.quadraticOperator ψ B.val).injective.eq_iff.symm

def quadraticOscillator [CharZero k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k]
    (hUnitary : ∀ t : k, ‖ψ t‖ = 1) (B : Weil.Local.FunctionsMetaplectic.Construction.SymmetricMatrix k n) : Weil.Local.FunctionsMetaplectic.Construction.Oscillator k n ψ :=
  ⟨(Weil.Local.Generators.Construction.quadraticSymplectic B, testQuadratic ψ hStable B.val), by
    constructor
    · intro f
      unfold Weil.Local.FunctionsMetaplectic.Construction.l2Energy
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        change ‖Weil.Local.FunctionsMetaplectic.Construction.quadraticOperator ψ B.val f.val x‖ ^ 2 = ‖f.val x‖ ^ 2
        rw [Weil.Local.Generators.Construction.quadraticOperator_norm ψ hUnitary]
    · exact testQuadratic_intertwines ψ hStable B⟩

end

section

/-! Locally constant test functions and actual quadratic lifts at nonarchimedean places. -/

open OAI.RepresentationTheory.Weil.Local.Generators.Construction

open _root_.MeasureTheory Filter
open scoped _root_.Topology

theorem schwartzBruhat_totallyDisconnected_iff
    {k : Type} [NormedField k] [TotallyDisconnectedSpace k] {n : ℕ}
    {f : Weil.Local.FunctionsMetaplectic.Construction.Position k n → ℂ} :
    f ∈ Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k n ↔ IsLocallyConstant f ∧ HasCompactSupport f := by
  constructor
  · intro hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
        rcases hf with hf | ⟨d, e, φ, rfl⟩
        · exact hf
        · have hs : IsPreconnected (Set.univ : Set (Weil.Local.FunctionsMetaplectic.Construction.Position k n)) := by
            rw [← e.surjective.range_eq, ← Set.image_univ]
            exact isPreconnected_univ.image e e.continuous.continuousOn
          let : Subsingleton (Weil.Local.FunctionsMetaplectic.Construction.Position k n) := Set.subsingleton_of_univ_subsingleton hs.subsingleton
          constructor
          · exact IsLocallyConstant.of_constant _
              (fun x y => congrArg (fun z => φ (e.symm z)) (Subsingleton.elim x y))
          · exact HasCompactSupport.of_compactSpace _
    | zero => exact ⟨IsLocallyConstant.const 0,
        HasCompactSupport.intro isCompact_empty (fun _ _ => rfl)⟩
    | add f g _ _ hf hg => exact ⟨hf.1.add hg.1, hf.2.add hg.2⟩
    | smul c f _ hf =>
        exact ⟨hf.1.comp (fun z => c * z), hf.2.smul_left⟩
  · exact fun hf => Weil.Local.FunctionsMetaplectic.Construction.compact_locallyConstant_mem hf.1 hf.2

theorem nonarchimedean_character_locallyConstant
    {k : Type} [NormedField k] [NonarchimedeanAddGroup k]
    (ψ : AddChar k ℂ) (hUnitary : ∀ t : k, ‖ψ t‖ = 1)
    (hContinuous : Continuous (fun t => ψ t)) : IsLocallyConstant (fun t => ψ t) := by
  let χ := FourierTools.LocalAnalysis.circleCharacter ψ hUnitary
  have hχ : Continuous χ := FourierTools.LocalAnalysis.circleCharacter_continuous ψ hUnitary hContinuous
  have hzero : χ 0 ∈ Circle.centeredArc (Real.pi / 2) := by
    rw [χ.map_zero_eq_one]
    exact ⟨0, by simpa using (half_pos Real.pi_pos), Circle.exp_zero⟩
  have hn : χ ⁻¹' Circle.centeredArc (Real.pi / 2) ∈ 𝓝 (0 : k) :=
    ((Circle.isOpen_centeredArc _).preimage hχ).mem_nhds hzero
  obtain ⟨U, hU⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ hn
  have hker (t : k) (ht : t ∈ U) : ψ t = 1 := by
    have h : χ t = 1 := Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two (fun m _ => by
      rw [← χ.map_nsmul_eq_pow]
      exact hU (U.nsmul_mem ht m))
    exact congrArg (fun z : Circle => (z : ℂ)) h
  rw [IsLocallyConstant.iff_eventually_eq]
  intro t
  have hnh : ∀ᶠ y in 𝓝 t, y - t ∈ U := by
    exact (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds
      (by simpa using U.isOpen.mem_nhds U.zero_mem)
  filter_upwards [hnh] with y hy
  have hh := ψ.map_add_eq_mul (y - t) t
  simpa [hker (y - t) hy] using hh

theorem nonarchimedean_quadratic_mem
    {k : Type} [NormedField k] [NonarchimedeanAddGroup k] {n : ℕ}
    (ψ : AddChar k ℂ) (hUnitary : ∀ t : k, ‖ψ t‖ = 1)
    (hContinuous : Continuous (fun t => ψ t))
    (B : Matrix (Fin n) (Fin n) k) (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    Weil.Local.FunctionsMetaplectic.Construction.quadraticOperator ψ B f.val ∈ Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k n := by
  obtain ⟨hf, hs⟩ := schwartzBruhat_totallyDisconnected_iff.mp f.property
  apply Weil.Local.FunctionsMetaplectic.Construction.compact_locallyConstant_mem
  · exact ((nonarchimedean_character_locallyConstant ψ hUnitary hContinuous).comp_continuous
      (show Continuous (Weil.Local.FunctionsMetaplectic.Construction.quadratic B) by unfold Weil.Local.FunctionsMetaplectic.Construction.quadratic; fun_prop)).mul hf
  · exact hs.mul_left

end

/-! Compact locally constant Fourier analysis from small translations. -/

open OAI.RepresentationTheory.Weil.Local.Generators.Construction

open _root_.MeasureTheory Filter
open scoped _root_.Topology

theorem character_finset_sum {k ι : Type*} [AddCommMonoid k]
    (ψ : AddChar k ℂ) (s : Finset ι) (a : ι → k) :
    ψ (∑ i ∈ s, a i) = ∏ i ∈ s, ψ (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp only [Finset.sum_insert hi, Finset.prod_insert hi, ψ.map_add_eq_mul, ih]

theorem compact_locallyConstant_translation
    {E : Type*} [NormedAddCommGroup E] {f : E → ℂ}
    (hf : IsLocallyConstant f) (hs : HasCompactSupport f) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x t : E, ‖t‖ < ε → f (x + t) = f x := by
  let : UniformSpace ℂ := ⊥
  have hu : UniformContinuous f := hs.uniformContinuous_of_continuous hf.continuous
  have h : {p : E × E | f p.1 = f p.2} ∈ uniformity E :=
    hu (DiscreteUniformity.relId_mem_uniformity ℂ)
  obtain ⟨ε, hε, heq⟩ := Metric.mem_uniformity_dist.mp h
  refine ⟨ε, hε, fun x t ht => heq (a := x + t) (b := x) ?_⟩
  simpa [dist_eq_norm] using ht

theorem fourierIntegral_translate
    {k : Type} [NormedField k] [MeasurableSpace k] [BorelSpace k]
    [SecondCountableTopology k] {n : ℕ}
    (ψ : AddChar k ℂ) (μ : Measure (Weil.Local.FunctionsMetaplectic.Construction.Position k n)) [μ.IsAddHaarMeasure]
    (f : Weil.Local.FunctionsMetaplectic.Construction.Position k n → ℂ) (t x : Weil.Local.FunctionsMetaplectic.Construction.Position k n) :
    Weil.Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ (fun y => f (y + t)) x = ψ (Weil.Local.FunctionsMetaplectic.Construction.dot x t) * Weil.Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f x := by
  unfold Weil.Local.FunctionsMetaplectic.Construction.fourierIntegral
  rw [← integral_const_mul]
  have h := integral_add_right_eq_self (μ := μ)
    (fun y => ψ (Weil.Local.FunctionsMetaplectic.Construction.dot x t) * (f y * ψ (-Weil.Local.FunctionsMetaplectic.Construction.dot x y))) t
  rw [← h]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    dsimp only
    have hp : Weil.Local.FunctionsMetaplectic.Construction.dot x (y + t) = Weil.Local.FunctionsMetaplectic.Construction.dot x y + Weil.Local.FunctionsMetaplectic.Construction.dot x t := by
      simp [Weil.Local.FunctionsMetaplectic.Construction.dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    rw [hp, neg_add, ψ.map_add_eq_mul]
    have hc : ψ (Weil.Local.FunctionsMetaplectic.Construction.dot x t) * ψ (-Weil.Local.FunctionsMetaplectic.Construction.dot x t) = 1 := by
      rw [← ψ.map_add_eq_mul]
      simp
    linear_combination -(f (y + t) * ψ (-Weil.Local.FunctionsMetaplectic.Construction.dot x y)) * hc

theorem fourierIntegral_vanishes_of_translation
    {k : Type} [NormedField k] [MeasurableSpace k] [BorelSpace k]
    [SecondCountableTopology k] {n : ℕ}
    (ψ : AddChar k ℂ) (μ : Measure (Weil.Local.FunctionsMetaplectic.Construction.Position k n)) [μ.IsAddHaarMeasure]
    (f : Weil.Local.FunctionsMetaplectic.Construction.Position k n → ℂ) (t x : Weil.Local.FunctionsMetaplectic.Construction.Position k n)
    (ht : ∀ y, f (y + t) = f y) (hx : ψ (Weil.Local.FunctionsMetaplectic.Construction.dot x t) ≠ 1) :
    Weil.Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f x = 0 := by
  have h := fourierIntegral_translate ψ μ f t x
  have heq : (fun y => f (y + t)) = f := funext ht
  rw [heq] at h
  by_contra hn
  apply hx
  apply mul_right_cancel₀ hn
  simpa using h.symm

theorem fourierIntegral_compactSupport_of_locallyConstant
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k]
    [ProperSpace k] [SecondCountableTopology k] {n : ℕ}
    (ψ : AddChar k ℂ) (hNontrivial : ∃ a : k, ψ a ≠ 1)
    (μ : Measure (Weil.Local.FunctionsMetaplectic.Construction.Position k n)) [μ.IsAddHaarMeasure]
    {f : Weil.Local.FunctionsMetaplectic.Construction.Position k n → ℂ} (hf : IsLocallyConstant f) (hs : HasCompactSupport f) :
    HasCompactSupport (Weil.Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f) := by
  obtain ⟨ε, hε, heq⟩ := compact_locallyConstant_translation hf hs
  obtain ⟨a, ha⟩ := hNontrivial
  have hR : 0 ≤ ‖a‖ / ε := div_nonneg (norm_nonneg _) hε.le
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : Weil.Local.FunctionsMetaplectic.Construction.Position k n) (‖a‖ / ε))
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  intro i
  by_contra! hi
  have hxi : x i ≠ 0 := norm_pos_iff.mp (lt_of_le_of_lt hR hi)
  let t : Weil.Local.FunctionsMetaplectic.Construction.Position k n := Pi.single i (a / x i)
  have ht : ‖t‖ < ε := by
    rw [show ‖t‖ = ‖a / x i‖ from Pi.norm_single _, norm_div]
    apply (div_lt_iff₀ (norm_pos_iff.mpr hxi)).mpr
    simpa only [mul_comm] using (div_lt_iff₀ hε).mp hi
  have hdot : Weil.Local.FunctionsMetaplectic.Construction.dot x t = a := by
    simp only [Weil.Local.FunctionsMetaplectic.Construction.dot, t, Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
    field_simp
  have hzero := fourierIntegral_vanishes_of_translation ψ μ f t x
    (fun y => heq y t ht) (by rwa [hdot])
  exact hx hzero

theorem fourierIntegral_locallyConstant
    {k : Type} [NormedField k] [MeasurableSpace k] {n : ℕ}
    (ψ : AddChar k ℂ) (hψ : IsLocallyConstant (fun t => ψ t))
    (μ : Measure (Weil.Local.FunctionsMetaplectic.Construction.Position k n))
    {f : Weil.Local.FunctionsMetaplectic.Construction.Position k n → ℂ} (hs : HasCompactSupport f) :
    IsLocallyConstant (Weil.Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f) := by
  obtain ⟨R, hR, hbound⟩ := hs.isBounded.exists_pos_norm_le
  obtain ⟨ε, hε, hker⟩ := Metric.eventually_nhds_iff.mp (hψ.eventually_eq 0)
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  apply Metric.eventually_nhds_iff.mpr
  refine ⟨ε / R, div_pos hε hR, fun y hy => ?_⟩
  unfold Weil.Local.FunctionsMetaplectic.Construction.fourierIntegral
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    dsimp only
    by_cases hz : f z = 0
    · simp [hz]
    have hzR : ‖z‖ ≤ R := hbound z (subset_tsupport f hz)
    have hsmall : ‖y - x‖ * R < ε :=
      (lt_div_iff₀ hR).mp (by simpa [dist_eq_norm] using hy)
    have hchar : ψ (-Weil.Local.FunctionsMetaplectic.Construction.dot (y - x) z) = 1 := by
      rw [Weil.Local.FunctionsMetaplectic.Construction.dot, ← Finset.sum_neg_distrib, character_finset_sum]
      apply Finset.prod_eq_one
      intro i _
      have hnorm : ‖-((y - x) i * z i)‖ < ε := by
        rw [norm_neg, norm_mul]
        calc
          _ ≤ ‖y - x‖ * R := mul_le_mul
            (norm_le_pi_norm (y - x) i) ((norm_le_pi_norm z i).trans hzR)
            (norm_nonneg _) (norm_nonneg _)
          _ < ε := hsmall
      simpa only [ψ.map_zero_eq_one] using hker
        (show dist (-((y - x) i * z i)) 0 < ε by simpa using hnorm)
    have hsplit : -Weil.Local.FunctionsMetaplectic.Construction.dot y z = -Weil.Local.FunctionsMetaplectic.Construction.dot x z + -Weil.Local.FunctionsMetaplectic.Construction.dot (y - x) z := by
      simp only [Weil.Local.FunctionsMetaplectic.Construction.dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
      ring
    rw [hsplit, ψ.map_add_eq_mul, hchar, mul_one]

/-- The Fourier integral preserves the actual nonarchimedean Bruhat space. -/
theorem nonarchimedean_fourier_mem
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] [NonarchimedeanAddGroup k]
    [ProperSpace k] [SecondCountableTopology k] {n : ℕ}
    (ψ : AddChar k ℂ) (hUnitary : ∀ t : k, ‖ψ t‖ = 1)
    (hContinuous : Continuous (fun t => ψ t)) (hNontrivial : ∃ t : k, ψ t ≠ 1)
    (μ : Measure (Weil.Local.FunctionsMetaplectic.Construction.Position k n)) [μ.IsAddHaarMeasure] (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    Weil.Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f.val ∈ Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k n := by
  obtain ⟨hf, hs⟩ := schwartzBruhat_totallyDisconnected_iff.mp f.property
  exact Weil.Local.FunctionsMetaplectic.Construction.compact_locallyConstant_mem
    (fourierIntegral_locallyConstant ψ
      (nonarchimedean_character_locallyConstant ψ hUnitary hContinuous) μ hs)
    (fourierIntegral_compactSupport_of_locallyConstant ψ hNontrivial μ hf hs)

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.NonarchimedeanIntertwiner.LocalAnalysis
