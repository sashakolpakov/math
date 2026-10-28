import OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor
import Mathlib.Algebra.Homology.Homotopy

/-! # Coordinate Homotopy -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.CoordinateHomotopy.KoszulCoordinateHomotopy

noncomputable section

/-!
# A coordinate homotopy for the tensor differential complex

An integral right inverse of one coordinate derivative, commuting with
the other derivatives, combines with exterior contraction. Its homotopy
identity leaves the coefficient and exterior parts constant in that coordinate.
-/

open scoped TensorProduct
open _root_.CategoryTheory

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor

universe u

theorem tensor_split_identity {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (a b : M) (u v w : N) (huv : u + v = w) :
    b ⊗ₜ[R] u + a ⊗ₜ[R] v + (a - b) ⊗ₜ[R] (w - v) = a ⊗ₜ[R] w := by
  rw [← huv, add_sub_cancel_right, TensorProduct.sub_tmul, TensorProduct.tmul_add]
  abel

variable (R σ M : Type u) [CommRing R] [AddCommGroup M] [Module R M] [Fintype σ]
  (D : σ → Module.End R M) (i : σ) (S : Module.End R M)

def exteriorContraction (n : ℕ) : (⋀[R]^(n + 1) (σ →₀ R)) →ₗ[R] (⋀[R]^n (σ →₀ R)) :=
  ExteriorContractionCoe.ExteriorContraction.contraction R (σ →₀ R) (Finsupp.lapply i) n

def homotopyMap (n : ℕ) : Tensor.KoszulTensor.Term R σ M (n + 1) →ₗ[R] Tensor.KoszulTensor.Term R σ M n :=
  TensorProduct.map S (exteriorContraction R σ i n)

def coefficientProjection : Module.End R M := LinearMap.id - S.comp (D i)

def exteriorProjection : (n : ℕ) → Module.End R (⋀[R]^n (σ →₀ R))
  | 0 => LinearMap.id
  | n + 1 => LinearMap.id - (Tensor.KoszulTensor.exteriorWedge R σ i n).comp (exteriorContraction R σ i n)

def projectionMap (n : ℕ) : Module.End R (Tensor.KoszulTensor.Term R σ M n) :=
  TensorProduct.map (coefficientProjection R σ M D i S) (exteriorProjection R σ i n)

omit [Fintype σ] in
theorem contraction_wedge_zero (j : σ) (ω : ⋀[R]^0 (σ →₀ R)) :
    exteriorContraction R σ i 0 (Tensor.KoszulTensor.exteriorWedge R σ j 0 ω) = (Finsupp.single j (1 : R)) i • ω :=
  ExteriorContractionCoe.ExteriorContraction.contraction_wedge_zero R (σ →₀ R) (Finsupp.lapply i) (Finsupp.single j 1) ω

omit [Fintype σ] in
theorem contraction_wedge (j : σ) (n : ℕ) (ω : ⋀[R]^(n + 1) (σ →₀ R)) :
    exteriorContraction R σ i (n + 1) (Tensor.KoszulTensor.exteriorWedge R σ j (n + 1) ω) +
      Tensor.KoszulTensor.exteriorWedge R σ j n (exteriorContraction R σ i n ω) = (Finsupp.single j (1 : R)) i • ω :=
  ExteriorContractionCoe.ExteriorContraction.contraction_wedge R (σ →₀ R) (Finsupp.lapply i) (Finsupp.single j 1) n ω

theorem homotopy_zero_linear :
    (homotopyMap R σ M i S 0).comp (Tensor.KoszulTensor.differential R σ M D 0) + projectionMap R σ M D i S 0 =
      LinearMap.id := by
  classical
  apply TensorProduct.ext
  apply LinearMap.ext
  intro m
  apply LinearMap.ext
  intro ω
  change homotopyMap R σ M i S 0 (Tensor.KoszulTensor.differential R σ M D 0 (m ⊗ₜ[R] ω)) +
    projectionMap R σ M D i S 0 (m ⊗ₜ[R] ω) = m ⊗ₜ[R] ω
  rw [Tensor.KoszulTensor.differential_tmul, map_sum]
  have hterm (j : σ) : homotopyMap R σ M i S 0 (D j m ⊗ₜ[R] Tensor.KoszulTensor.exteriorWedge R σ j 0 ω) =
      if j = i then S (D i m) ⊗ₜ[R] ω else 0 := by
    change S (D j m) ⊗ₜ[R] exteriorContraction R σ i 0 (Tensor.KoszulTensor.exteriorWedge R σ j 0 ω) = _
    rw [contraction_wedge_zero]
    by_cases hji : j = i
    · subst j
      simp only [Finsupp.single_eq_same, one_smul]
      rfl
    · rw [Finsupp.single_eq_of_ne (Ne.symm hji), zero_smul, TensorProduct.tmul_zero, ite_eq_right hji]
  simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  change S (D i m) ⊗ₜ[R] ω + (m - S (D i m)) ⊗ₜ[R] ω = m ⊗ₜ[R] ω
  rw [TensorProduct.sub_tmul]
  abel

variable (hright : ∀ m, D i (S m) = m)
  (hcommS : ∀ j, j ≠ i → ∀ m, D j (S m) = S (D j m))

include hright hcommS in
theorem homotopy_succ_linear (n : ℕ) :
    (homotopyMap R σ M i S (n + 1)).comp (Tensor.KoszulTensor.differential R σ M D (n + 1)) +
      (Tensor.KoszulTensor.differential R σ M D n).comp (homotopyMap R σ M i S n) +
        projectionMap R σ M D i S (n + 1) = LinearMap.id := by
  classical
  apply TensorProduct.ext
  apply LinearMap.ext
  intro m
  apply LinearMap.ext
  intro ω
  have hsum : (∑ j, (S (D j m) ⊗ₜ[R]
        exteriorContraction R σ i (n + 1) (Tensor.KoszulTensor.exteriorWedge R σ j (n + 1) ω) +
      D j (S m) ⊗ₜ[R] Tensor.KoszulTensor.exteriorWedge R σ j n (exteriorContraction R σ i n ω))) =
      S (D i m) ⊗ₜ[R] exteriorContraction R σ i (n + 1) (Tensor.KoszulTensor.exteriorWedge R σ i (n + 1) ω) +
        D i (S m) ⊗ₜ[R] Tensor.KoszulTensor.exteriorWedge R σ i n (exteriorContraction R σ i n ω) := by
    apply Finset.sum_eq_single i
    · intro j _ hji
      rw [hcommS j hji m, ← TensorProduct.tmul_add, contraction_wedge,
        Finsupp.single_eq_of_ne (Ne.symm hji), zero_smul, TensorProduct.tmul_zero]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  change homotopyMap R σ M i S (n + 1) (Tensor.KoszulTensor.differential R σ M D (n + 1) (m ⊗ₜ[R] ω)) +
    Tensor.KoszulTensor.differential R σ M D n (homotopyMap R σ M i S n (m ⊗ₜ[R] ω)) +
      projectionMap R σ M D i S (n + 1) (m ⊗ₜ[R] ω) = m ⊗ₜ[R] ω
  rw [Tensor.KoszulTensor.differential_tmul, map_sum]
  change (∑ j, S (D j m) ⊗ₜ[R]
      exteriorContraction R σ i (n + 1) (Tensor.KoszulTensor.exteriorWedge R σ j (n + 1) ω)) +
    Tensor.KoszulTensor.differential R σ M D n (S m ⊗ₜ[R] exteriorContraction R σ i n ω) +
      (m - S (D i m)) ⊗ₜ[R] (ω - Tensor.KoszulTensor.exteriorWedge R σ i n (exteriorContraction R σ i n ω)) = _
  rw [Tensor.KoszulTensor.differential_tmul, ← Finset.sum_add_distrib, hsum, hright]
  apply tensor_split_identity
  simpa only [Finsupp.single_eq_same, one_smul] using contraction_wedge R σ i i n ω

variable (hcomm : ∀ j k, Function.Commute (D j) (D k))

local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.complex R σ M D hcomm

def homotopyFamily (a b : ℕ) (hab : (ComplexShape.up ℕ).Rel b a) : (K).X a ⟶ (K).X b := by
  have he : b + 1 = a := hab
  subst a
  exact ModuleCat.ofHom (homotopyMap R σ M i S b)

theorem homotopyFamily_succ (n : ℕ) :
    homotopyFamily R σ M D i S hcomm (n + 1) n rfl = ModuleCat.ofHom (homotopyMap R σ M i S n) := rfl

def boundary : K ⟶ K := Homotopy.nullHomotopicMap' (homotopyFamily R σ M D i S hcomm)

/-- The coordinate projection as an actual cochain map. -/
def projectionChain : K ⟶ K := 𝟙 K - boundary R σ M D i S hcomm

/-- The coordinate projection is homotopic to the identity. -/
def homotopy : Homotopy (𝟙 K) (projectionChain R σ M D i S hcomm) := by
  refine (Homotopy.equivSubZero (f := 𝟙 K) (g := projectionChain R σ M D i S hcomm)).symm ?_
  simpa only [projectionChain, sub_sub_cancel, boundary] using
    Homotopy.nullHomotopy' (homotopyFamily R σ M D i S hcomm)

theorem complex_d (n : ℕ) : (K).d n (n + 1) = ModuleCat.ofHom (Tensor.KoszulTensor.differential R σ M D n) :=
  CochainComplex.of_d (fun n => ModuleCat.of R (Tensor.KoszulTensor.Term R σ M n))
    (fun n => ModuleCat.ofHom (Tensor.KoszulTensor.differential R σ M D n)) n

theorem boundary_zero : (boundary R σ M D i S hcomm).f 0 =
    ModuleCat.ofHom ((homotopyMap R σ M i S 0).comp (Tensor.KoszulTensor.differential R σ M D 0)) := by
  have hzero : ∀ l : ℕ, ¬ (ComplexShape.up ℕ).Rel l 0 := by
    intro l hl
    change l + 1 = 0 at hl
    omega
  have hb := Homotopy.nullHomotopicMap'_f_of_not_rel_right
    (show (ComplexShape.up ℕ).Rel 0 1 from rfl) hzero (homotopyFamily R σ M D i S hcomm)
  change (boundary R σ M D i S hcomm).f 0 = (K).d 0 1 ≫
    ModuleCat.ofHom (homotopyMap R σ M i S 0) at hb
  exact hb.trans (congrArg (fun f : (K).X 0 ⟶ (K).X 1 =>
    f ≫ (show (K).X 1 ⟶ (K).X 0 from ModuleCat.ofHom (homotopyMap R σ M i S 0)))
      (complex_d R σ M D hcomm 0))

theorem boundary_succ (n : ℕ) : (boundary R σ M D i S hcomm).f (n + 1) =
    ModuleCat.ofHom ((homotopyMap R σ M i S (n + 1)).comp (Tensor.KoszulTensor.differential R σ M D (n + 1)) +
      (Tensor.KoszulTensor.differential R σ M D n).comp (homotopyMap R σ M i S n)) := by
  have hb := Homotopy.nullHomotopicMap'_f
    (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl)
    (show (ComplexShape.up ℕ).Rel (n + 1) (n + 2) from rfl) (homotopyFamily R σ M D i S hcomm)
  change (boundary R σ M D i S hcomm).f (n + 1) = (K).d (n + 1) (n + 2) ≫
    (show (K).X (n + 2) ⟶ (K).X (n + 1) from ModuleCat.ofHom (homotopyMap R σ M i S (n + 1))) +
      (show (K).X (n + 1) ⟶ (K).X n from ModuleCat.ofHom (homotopyMap R σ M i S n)) ≫
        (K).d n (n + 1) at hb
  exact hb.trans (congrArg₂ (fun (f : (K).X (n + 1) ⟶ (K).X (n + 2))
    (g : (K).X n ⟶ (K).X (n + 1)) =>
      f ≫ (show (K).X (n + 2) ⟶ (K).X (n + 1) from ModuleCat.ofHom (homotopyMap R σ M i S (n + 1))) +
        (show (K).X (n + 1) ⟶ (K).X n from ModuleCat.ofHom (homotopyMap R σ M i S n)) ≫ g)
    (complex_d R σ M D hcomm (n + 1)) (complex_d R σ M D hcomm n))

include hright hcommS in
/-- In each degree, the cochain projection is the explicit tensor of the two coordinate projections. -/
theorem projectionChain_f (n : ℕ) :
    (projectionChain R σ M D i S hcomm).f n = ModuleCat.ofHom (projectionMap R σ M D i S n) := by
  have hb : (show Module.End R (Tensor.KoszulTensor.Term R σ M n) from ((boundary R σ M D i S hcomm).f n).hom) +
      projectionMap R σ M D i S n = LinearMap.id := by
    cases n with
    | zero =>
      have hzero := congrArg (fun f : (K).X 0 ⟶ (K).X 0 => f.hom) (boundary_zero R σ M D i S hcomm)
      exact (congrArg (fun f : Module.End R (Tensor.KoszulTensor.Term R σ M 0) => f + projectionMap R σ M D i S 0)
        hzero).trans (homotopy_zero_linear R σ M D i S)
    | succ n =>
      have hsucc := congrArg (fun f : (K).X (n + 1) ⟶ (K).X (n + 1) => f.hom)
        (boundary_succ R σ M D i S hcomm n)
      exact (congrArg (fun f : Module.End R (Tensor.KoszulTensor.Term R σ M (n + 1)) => f + projectionMap R σ M D i S (n + 1))
        hsucc).trans (homotopy_succ_linear R σ M D i S hright hcommS n)
  apply ModuleCat.hom_ext
  change LinearMap.id - (show Module.End R (Tensor.KoszulTensor.Term R σ M n) from
    ((boundary R σ M D i S hcomm).f n).hom) = projectionMap R σ M D i S n
  exact sub_eq_iff_eq_add.mpr (hb.symm.trans (add_comm _ _))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.CoordinateHomotopy.KoszulCoordinateHomotopy
