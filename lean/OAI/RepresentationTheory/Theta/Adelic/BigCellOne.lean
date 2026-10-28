import OAI.RepresentationTheory.Weil.AdelicSplitting.SymplecticGeneration

/-! # Big Cell One -/

namespace OAI.RepresentationTheory.Theta.Adelic.BigCellOne

noncomputable section

/-! Continuous Gauss coordinates near the identity of the symplectic group. -/

open OAI.RepresentationTheory.Weil.AdelicSplitting.SymplecticGeneration
open scoped _root_.Topology

variable {k : Type} [NormedField k] {N : ℕ}

@[simp] theorem one_block11 :
    (1 : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) k).toBlocks₁₁ = 1 := by
  ext i j
  simp [Matrix.toBlocks₁₁, Matrix.one_apply]

@[simp] theorem one_block12 :
    (1 : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) k).toBlocks₁₂ = 0 := by
  ext i j
  simp [Matrix.toBlocks₁₂]

@[simp] theorem one_block21 :
    (1 : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) k).toBlocks₂₁ = 0 := by
  ext i j
  simp [Matrix.toBlocks₂₁]

@[fun_prop] theorem continuous_block11 {X : Type*} [TopologicalSpace X]
    {A : X → Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) k} (hA : Continuous A) :
    Continuous (fun x => (A x).toBlocks₁₁) := by
  exact continuous_pi fun i => continuous_pi fun j =>
    (continuous_apply (Sum.inl j)).comp ((continuous_apply (Sum.inl i)).comp hA)

@[fun_prop] theorem continuous_block12 {X : Type*} [TopologicalSpace X]
    {A : X → Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) k} (hA : Continuous A) :
    Continuous (fun x => (A x).toBlocks₁₂) := by
  exact continuous_pi fun i => continuous_pi fun j =>
    (continuous_apply (Sum.inr j)).comp ((continuous_apply (Sum.inl i)).comp hA)

@[fun_prop] theorem continuous_block21 {X : Type*} [TopologicalSpace X]
    {A : X → Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) k} (hA : Continuous A) :
    Continuous (fun x => (A x).toBlocks₂₁) := by
  exact continuous_pi fun i => continuous_pi fun j =>
    (continuous_apply (Sum.inl j)).comp ((continuous_apply (Sum.inr i)).comp hA)

def BigCell := {g : Weil.Local.FunctionsMetaplectic.Construction.Symplectic k N | IsUnit g.val.toBlocks₁₁.det}

def identity : BigCell (k := k) (N := N) := by
  refine ⟨1, ?_⟩
  change IsUnit ((1 : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) k).toBlocks₁₁.det)
  simp

def linearPart (g : BigCell (k := k) (N := N)) : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k N :=
  g.val.val.toBlocks₁₁.nonsingInvUnit g.property

theorem linearPart_val (g : BigCell (k := k) (N := N)) :
    (linearPart g).val = g.val.val.toBlocks₁₁ := rfl

@[fun_prop] theorem linearPart_continuous :
    Continuous (linearPart (k := k) (N := N)) := by
  have hv : Continuous (fun g : BigCell (k := k) (N := N) => g.val.val.toBlocks₁₁) := by
    fun_prop
  apply Units.continuous_iff.mpr
  constructor
  · change Continuous (fun g : BigCell (k := k) (N := N) => g.val.val.toBlocks₁₁)
    exact hv
  · simp_rw [Matrix.coe_units_inv, linearPart_val]
    apply continuous_iff_continuousAt.mpr
    intro g
    have hi : ContinuousAt Inv.inv g.val.val.toBlocks₁₁ :=
      continuousAt_matrix_inv _ (by
        rw [Ring.inverse_eq_inv']
        exact continuousAt_inv₀ g.property.ne_zero)
    exact hi.comp (f := fun a : BigCell (k := k) (N := N) => a.val.val.toBlocks₁₁)
      (hv.continuousAt (x := g))

def lowerPart (g : BigCell (k := k) (N := N)) : Matrix (Fin N) (Fin N) k :=
  g.val.val.toBlocks₂₁ * ((linearPart g)⁻¹).val

def upperPart (g : BigCell (k := k) (N := N)) : Matrix (Fin N) (Fin N) k :=
  ((linearPart g)⁻¹).val * g.val.val.toBlocks₁₂

theorem lowerPart_continuous : Continuous (lowerPart (k := k) (N := N)) := by
  unfold lowerPart
  exact (continuous_block21 (continuous_subtype_val.comp continuous_subtype_val)).mul
    (Units.continuous_coe_inv.comp linearPart_continuous)

theorem upperPart_continuous : Continuous (upperPart (k := k) (N := N)) := by
  unfold upperPart
  exact (Units.continuous_coe_inv.comp linearPart_continuous).mul
    (continuous_block12 (continuous_subtype_val.comp continuous_subtype_val))

@[simp] theorem linearPart_identity :
    linearPart (identity (k := k) (N := N)) = 1 := by
  apply Units.ext
  change (1 : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) k).toBlocks₁₁ = 1
  exact one_block11

@[simp] theorem lowerPart_identity :
    lowerPart (identity (k := k) (N := N)) = 0 := by
  unfold lowerPart
  rw [linearPart_identity]
  change (1 : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) k).toBlocks₂₁ * 1 = 0
  simp

@[simp] theorem upperPart_identity :
    upperPart (identity (k := k) (N := N)) = 0 := by
  unfold upperPart
  rw [linearPart_identity]
  change 1 * (1 : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) k).toBlocks₁₂ = 0
  simp

theorem parameters_symmetric (g : BigCell (k := k) (N := N)) :
    (lowerPart g).IsSymm ∧ (upperPart g).IsSymm :=
  Weil.AdelicSplitting.SymplecticGeneration.bigCell_parameters_symmetric (linearPart g) g.val.val.toBlocks₁₂
    g.val.val.toBlocks₂₁ g.val.val.toBlocks₂₂
    (by simpa only [linearPart_val, Matrix.fromBlocks_toBlocks] using g.val.property)

theorem factorization (g : BigCell (k := k) (N := N)) :
    g.val = Weil.AdelicSplitting.SymplecticGeneration.lower (lowerPart g) (parameters_symmetric g).1 *
      Weil.AdelicSplitting.SymplecticGeneration.levi (linearPart g) * Weil.AdelicSplitting.SymplecticGeneration.upper (upperPart g) (parameters_symmetric g).2 := by
  have h := Weil.AdelicSplitting.SymplecticGeneration.bigCell_factorization (linearPart g) g.val.val.toBlocks₁₂
    g.val.val.toBlocks₂₁ g.val.val.toBlocks₂₂
    (by simpa only [linearPart_val, Matrix.fromBlocks_toBlocks] using g.val.property)
  have heq : (⟨Matrix.fromBlocks (linearPart g).val g.val.val.toBlocks₁₂
      g.val.val.toBlocks₂₁ g.val.val.toBlocks₂₂,
      (by simpa only [linearPart_val, Matrix.fromBlocks_toBlocks] using g.val.property)⟩ :
      Weil.Local.FunctionsMetaplectic.Construction.Symplectic k N) = g.val := by
    apply Subtype.ext
    exact Matrix.fromBlocks_toBlocks g.val.val
  rw [heq] at h
  exact h

theorem inclusion_openEmbedding :
    Topology.IsOpenEmbedding (Subtype.val : BigCell (k := k) (N := N) → Weil.Local.FunctionsMetaplectic.Construction.Symplectic k N) := by
  apply IsOpen.isOpenEmbedding_subtypeVal
  change IsOpen {g : Weil.Local.FunctionsMetaplectic.Construction.Symplectic k N | IsUnit g.val.toBlocks₁₁.det}
  simp only [isUnit_iff_ne_zero]
  exact isOpen_ne.preimage (by fun_prop)

end

end OAI.RepresentationTheory.Theta.Adelic.BigCellOne
