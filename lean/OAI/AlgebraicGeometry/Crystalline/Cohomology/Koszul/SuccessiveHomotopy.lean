import OAI.AlgebraicGeometry.Crystalline.Cohomology.ExteriorCoordinate

/-! # Successive Homotopy -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.SuccessiveHomotopy.KoszulSuccessiveHomotopy

noncomputable section

/-!
# Composing coordinate contractions

Each coordinate projection is homotopic to the identity. Their finite
composition is again homotopic to the identity and vanishes in positive
degree when the list includes every coordinate.
-/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.CoordinateHomotopy.KoszulCoordinateHomotopy

universe u

variable (R σ M : Type u) [CommRing R] [AddCommGroup M] [Module R M] [Fintype σ]
  (D S : σ → Module.End R M) (hcomm : ∀ i j, Function.Commute (D i) (D j))

local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.complex R σ M D hcomm

def chain : List σ → (K ⟶ K)
  | [] => 𝟙 K
  | i :: l => CoordinateHomotopy.KoszulCoordinateHomotopy.projectionChain R σ M D i (S i) hcomm ≫ chain l

def homotopy : (l : List σ) → Homotopy (𝟙 K) (KoszulSuccessiveHomotopy.chain R σ M D S hcomm l)
  | [] => Homotopy.refl _
  | i :: l => (Homotopy.ofEq (Category.id_comp (𝟙 K)).symm).trans
      ((CoordinateHomotopy.KoszulCoordinateHomotopy.homotopy R σ M D i (S i) hcomm).comp
        (homotopy l))

def coefficient : List σ → Module.End R M
  | [] => LinearMap.id
  | i :: l => (coefficient l).comp (CoordinateHomotopy.KoszulCoordinateHomotopy.coefficientProjection R σ M D i (S i))

variable (hright : ∀ i m, D i (S i m) = m)
  (hcommS : ∀ i j, j ≠ i → ∀ m, D j (S i m) = S i (D j m))

include hright hcommS in
theorem chain_f (l : List σ) (n : ℕ) :
    (KoszulSuccessiveHomotopy.chain R σ M D S hcomm l).f n = ModuleCat.ofHom
      (TensorProduct.map (KoszulSuccessiveHomotopy.coefficient R σ M D S l) (ExteriorCoordinate.ExteriorCoordinateProjection.successive R σ l n)) := by
  induction l with
  | nil =>
    apply ModuleCat.hom_ext
    change LinearMap.id = TensorProduct.map LinearMap.id LinearMap.id
    exact TensorProduct.map_id.symm
  | cons i l ih =>
    change (CoordinateHomotopy.KoszulCoordinateHomotopy.projectionChain R σ M D i (S i) hcomm).f n ≫ (KoszulSuccessiveHomotopy.chain R σ M D S hcomm l).f n = _
    have hp := CoordinateHomotopy.KoszulCoordinateHomotopy.projectionChain_f R σ M D i (S i) (hright i) (hcommS i) hcomm n
    have he := congrArg₂ (fun f g : (K).X n ⟶ (K).X n => f ≫ g) hp ih
    apply he.trans
    apply ModuleCat.hom_ext
    exact (TensorProduct.map_comp _ _ _ _).symm

include hright hcommS in
theorem chain_positive (l : List σ) (hl : ∀ i, i ∈ l) (n : ℕ) :
    (KoszulSuccessiveHomotopy.chain R σ M D S hcomm l).f (n + 1) = 0 := by
  rw [chain_f R σ M D S hcomm hright hcommS,
    ExteriorCoordinate.ExteriorCoordinateProjection.successive_positive_eq_zero R σ l hl,
    TensorProduct.map_zero_right]
  rfl

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.SuccessiveHomotopy.KoszulSuccessiveHomotopy
