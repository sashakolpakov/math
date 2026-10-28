import OAI.NumberTheory.ArithmeticGroups.Lattices.MultilinearAction
import OAI.NumberTheory.ArithmeticGroups.Lattices.Archimedean.TensorStabilizer

/-! # Algebra Tensor Forms -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.AlgebraTensorForms.Construction

noncomputable section

section

/-! Scalar multiplication and the coefficient-algebra determinant as
finite-coordinate tensors, with their exact fixed-point conditions. -/

open scoped Classical

def scalarUnaryForm {R A : Type*} [Field R] [CommRing A] [Algebra R A] (n : ℕ) (a : A) :
    MultilinearMap R (fun _ : Fin 1 => Fin n → A) (Fin n → A) :=
  MultilinearMap.ofSubsingleton R (Fin n → A) (Fin n → A) (0 : Fin 1)
    (DistribSMul.toLinearMap R (Fin n → A) a)

def algebraDeterminantForm {R A : Type*} [Field R] [CommRing A] [Algebra R A] (n : ℕ) :
    MultilinearMap R (fun _ : Fin n => Fin n → A) A :=
  (Matrix.detRowAlternating (R := A) (n := Fin n)).toMultilinearMap.restrictScalars R

theorem algebraDeterminantForm_apply
    {R A : Type*} [Field R] [CommRing A] [Algebra R A] (n : ℕ) (v : Fin n → Fin n → A) :
    algebraDeterminantForm (R := R) n v = Matrix.det (Matrix.of v) := rfl

theorem fixed_scalarUnaryForm_iff
    {R A H I : Type*} [Field R] [CommRing A] [Algebra R A] [Group H] {n : ℕ}
    (ρ : H →* ((Fin n → A) ≃ₗ[R] (Fin n → A))) (b : Module.Basis I R (Fin n → A))
    (g : H) (a : A) :
    MultilinearAction.Construction.multilinearCovariantBasisRepresentation ρ ρ b 1 g
        (MultilinearBasisCoordinates.Construction.multilinearBasisEvaluationEquiv b 1 (scalarUnaryForm n a)) =
      MultilinearBasisCoordinates.Construction.multilinearBasisEvaluationEquiv b 1 (scalarUnaryForm n a) ↔
      ∀ x, ρ g (a • x) = a • ρ g x := by
  have hinv (x : Fin n → A) : ρ g⁻¹ (ρ g x) = x := by
    rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  have hfwd (x : Fin n → A) : ρ g (ρ g⁻¹ x) = x := by
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  rw [MultilinearAction.Construction.multilinearCovariantBasisRepresentation_fixed_iff]
  constructor
  · intro h x
    have he := h (fun _ => ρ g x)
    change ρ g (a • ρ g⁻¹ (ρ g x)) = a • ρ g x at he
    rwa [hinv] at he
  · intro h v
    change ρ g (a • ρ g⁻¹ (v 0)) = a • v 0
    rw [h, hfwd]

theorem fixed_algebraDeterminantForm_iff
    {R A H I : Type*} [Field R] [CommRing A] [Algebra R A] [Group H] {n : ℕ}
    (ρ : H →* ((Fin n → A) ≃ₗ[R] (Fin n → A))) (b : Module.Basis I R (Fin n → A))
    (g : H) :
    MultilinearAction.Construction.multilinearCovariantBasisRepresentation ρ (1 : H →* (A ≃ₗ[R] A)) b n g
        (MultilinearBasisCoordinates.Construction.multilinearBasisEvaluationEquiv b n (algebraDeterminantForm (R := R) n)) =
      MultilinearBasisCoordinates.Construction.multilinearBasisEvaluationEquiv b n (algebraDeterminantForm (R := R) n) ↔
      ∀ v : Fin n → Fin n → A,
        Matrix.det (Matrix.of (fun i => ρ g (v i))) = Matrix.det (Matrix.of v) := by
  have hinv (x : Fin n → A) : ρ g⁻¹ (ρ g x) = x := by
    rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  have hfwd (x : Fin n → A) : ρ g (ρ g⁻¹ x) = x := by
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  rw [MultilinearAction.Construction.multilinearCovariantBasisRepresentation_fixed_iff]
  change (∀ v, Matrix.det (Matrix.of (fun i => ρ g⁻¹ (v i))) = Matrix.det (Matrix.of v)) ↔ _
  constructor
  · intro h v
    have he := h (fun i => ρ g (v i))
    simp_rw [hinv] at he
    exact he.symm
  · intro h v
    have he := h (fun i => ρ g⁻¹ (v i))
    simp_rw [hfwd] at he
    exact he.symm

end

/-! The tensors defining the archimedean real image have integral values
on the standard Minkowski lattice. -/

open scoped Classical _root_.NumberField
open _root_.NumberField _root_.NumberField.mixedEmbedding

theorem matrix_det_mem_ringHom_range
    {R S I : Type*} [CommRing R] [CommRing S] [Fintype I] [DecidableEq I]
    (φ : R →+* S) (B : Matrix I I S) (hB : ∀ i j, B i j ∈ Set.range φ) :
    B.det ∈ Set.range φ := by
  choose C hC using hB
  let A : Matrix I I R := Matrix.of C
  refine ⟨A.det, ?_⟩
  rw [RingHom.map_det]
  congr 1
  ext i j : 1
  exact hC i j

theorem minkowski_lattice_smul_integer
    {k : Type} [Field k] [NumberField k] {n : ℕ} (a : 𝓞 k)
    {x : Fin n → mixedSpace k} (hx : x ∈ IntegralLattice.Construction.vectorLatticeImage (IntegralLattice.FullLattice.standard k n).module) :
    mixedEmbedding k (a : k) • x ∈ IntegralLattice.Construction.vectorLatticeImage (IntegralLattice.FullLattice.standard k n).module := by
  obtain ⟨v, hv, rfl⟩ := hx
  refine ⟨a • v, (IntegralLattice.FullLattice.standard k n).module.smul_mem a hv, ?_⟩
  funext i
  change mixedEmbedding k ((a : k) * v i) = mixedEmbedding k (a : k) * mixedEmbedding k (v i)
  exact map_mul _ _ _

theorem determinant_minkowski_lattice_integral
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (v : Fin n → Fin n → mixedSpace k)
    (hv : ∀ i, v i ∈ IntegralLattice.Construction.vectorLatticeImage (IntegralLattice.FullLattice.standard k n).module) :
    Matrix.det (Matrix.of v) ∈ mixedEmbedding.integerLattice k := by
  let φ := (mixedEmbedding k).comp (algebraMap (𝓞 k) k)
  have hm : ∀ i j, (Matrix.of v) i j ∈ Set.range φ := by
    intro i j
    have hi := hv i
    rw [Minkowski.IntegralAction.Construction.standard_vectorLatticeImage_eq_pi] at hi
    exact hi j trivial
  exact matrix_det_mem_ringHom_range φ (Matrix.of v) hm

theorem scalarUnaryForm_integral_coordinates
    {k : Type} {I : Type*} [Field k] [NumberField k] {n : ℕ}
    (b : Module.Basis I ℝ (Fin n → mixedSpace k))
    (hb : ∀ i, b i ∈ IntegralLattice.Construction.vectorLatticeImage (IntegralLattice.FullLattice.standard k n).module)
    (a : 𝓞 k) :
    MultilinearBasisCoordinates.Construction.multilinearBasisEvaluationEquiv b 1 (scalarUnaryForm n (mixedEmbedding k (a : k))) ∈
      MultilinearAction.Construction.integralMultilinearCoordinates b 1 (IntegralLattice.Construction.vectorLatticeImage (IntegralLattice.FullLattice.standard k n).module) := by
  apply (MultilinearAction.Construction.mem_integralMultilinearCoordinates _ _ _ _).mpr
  intro t
  change mixedEmbedding k (a : k) • b (t 0) ∈ _
  exact minkowski_lattice_smul_integer a (hb (t 0))

theorem algebraDeterminantForm_integral_coordinates
    {k : Type} {I : Type*} [Field k] [NumberField k] {n : ℕ}
    (b : Module.Basis I ℝ (Fin n → mixedSpace k))
    (hb : ∀ i, b i ∈ IntegralLattice.Construction.vectorLatticeImage (IntegralLattice.FullLattice.standard k n).module) :
    MultilinearBasisCoordinates.Construction.multilinearBasisEvaluationEquiv b n (algebraDeterminantForm (R := ℝ) n) ∈
      MultilinearAction.Construction.integralMultilinearCoordinates b n (mixedEmbedding.integerLattice k) := by
  apply (MultilinearAction.Construction.mem_integralMultilinearCoordinates _ _ _ _).mpr
  intro t
  change Matrix.det (Matrix.of (fun i => b (t i))) ∈ mixedEmbedding.integerLattice k
  exact determinant_minkowski_lattice_integral _ (fun i => hb (t i))

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.AlgebraTensorForms.Construction
