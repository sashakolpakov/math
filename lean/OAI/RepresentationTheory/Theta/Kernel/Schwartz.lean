import OAI.RepresentationTheory.Theta.Kernel.Factorization

/-! # Schwartz -/

namespace OAI.RepresentationTheory.Theta.Kernel.Schwartz

noncomputable section

open scoped BigOperators

universe u v

/-- Universe lifts let the two blocks have independent index universes. -/
def BinaryBlock (ι : Type u) (κ : Type v) : Bool → Type (max u v) :=
  Bool.rec (ULift.{v} (ι → Definitions.DerivativeFactorization.AQf)) (ULift.{u} (κ → Definitions.DerivativeFactorization.AQf))

instance (ι : Type u) (κ : Type v) (b : Bool) :
    TopologicalSpace (BinaryBlock ι κ b) := by
  cases b <;> dsimp [BinaryBlock] <;> infer_instance

def binaryCoordinates (ι : Type u) (κ : Type v) :
    ((b : Bool) → BinaryBlock ι κ b) ≃ₜ (Sum ι κ → Definitions.DerivativeFactorization.AQf) where
  toFun x := Sum.elim (x false).down (x true).down
  invFun a := fun b => by
    cases b
    · exact ULift.up (fun i => a (Sum.inl i))
    · exact ULift.up (fun j => a (Sum.inr j))
  left_inv x := by funext b; cases b <;> rfl
  right_inv a := by funext i; cases i <;> rfl
  continuous_toFun := by
    apply continuous_pi
    intro i
    cases i <;> dsimp <;> fun_prop
  continuous_invFun := by
    apply continuous_pi
    intro b
    cases b <;> fun_prop

/-- The conclusion of TensorDecomposition's `finite_product_decomposition`, specialized to
the two lifted blocks. The supplied prerequisite includes its topological
premises; only its resulting decomposition is needed in this implication. -/
def ProductInput (ι : Type u) (κ : Type v) : Prop :=
  ∀ φ : Definitions.DerivativeFactorization.FiniteSchwartz ((b : Bool) → BinaryBlock ι κ b),
    ∃ (n : ℕ) (c : Fin n → ℂ)
      (ψ : Fin n → (b : Bool) → Definitions.DerivativeFactorization.FiniteSchwartz (BinaryBlock ι κ b)),
      ∀ x, φ.1 x = ∑ j, c j * ∏ b, (ψ j b).1 (x b)

lemma e32_coordinates {ι : Type u} {κ : Type v}
    (h_TensorDecomposition : ProductInput ι κ) : Factorization.TensorDecompositionInput ι κ := by
  intro φ
  let e := binaryCoordinates ι κ
  let f : Definitions.DerivativeFactorization.FiniteSchwartz ((b : Bool) → BinaryBlock ι κ b) :=
    ⟨φ.1 ∘ e, φ.2.1.comp_continuous e.continuous, φ.2.2.comp_homeomorph e⟩
  obtain ⟨n, c, η, hη⟩ := h_TensorDecomposition f
  let ψ : Fin n → Definitions.DerivativeFactorization.Input ι := fun i =>
    ⟨(η i false).1 ∘ Homeomorph.ulift.symm,
      (η i false).2.1.comp_continuous Homeomorph.ulift.symm.continuous,
      (η i false).2.2.comp_homeomorph Homeomorph.ulift.symm⟩
  let χ : Fin n → Definitions.DerivativeFactorization.Input κ := fun i =>
    ⟨(η i true).1 ∘ Homeomorph.ulift.symm,
      (η i true).2.1.comp_continuous Homeomorph.ulift.symm.continuous,
      (η i true).2.2.comp_homeomorph Homeomorph.ulift.symm⟩
  refine ⟨n, c, ψ, χ, ?_⟩
  intro a
  have h := hη (e.symm a)
  simp only [f, Function.comp_apply, Homeomorph.apply_symm_apply, Fintype.prod_bool] at h
  change φ.1 a = ∑ j, c j *
    (η j false).1 (ULift.up (fun i => a (Sum.inl i))) *
    (η j true).1 (ULift.up (fun i => a (Sum.inr i)))
  change φ.1 a = ∑ j, c j *
    ((η j true).1 (ULift.up (fun i => a (Sum.inr i))) *
      (η j false).1 (ULift.up (fun i => a (Sum.inl i)))) at h
  simpa only [mul_comm, mul_left_comm, mul_assoc] using h

end

end OAI.RepresentationTheory.Theta.Kernel.Schwartz
