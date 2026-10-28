import Mathlib

/-! # Tensor Filtration -/

namespace OAI.NumberTheory.PadicHodge.WeakAdmissibility.TensorFiltration

noncomputable section

/-! Exhaustiveness and separation of the coefficient filtration on a tensor product. -/

open scoped TensorProduct
variable {R B V : Type*} [Field R] [AddCommGroup B] [Module R B]
  [AddCommGroup V] [Module R V]

def tensorStep (F : ℤ → Submodule R B) (i : ℤ) : Submodule R (B ⊗[R] V) :=
  Submodule.span R {x | ∃ b ∈ F i, ∃ v : V, b ⊗ₜ[R] v = x}

theorem tmul_mem_tensorStep (F : ℤ → Submodule R B) (i : ℤ) {b : B}
    (hb : b ∈ F i) (v : V) : b ⊗ₜ[R] v ∈ tensorStep F i :=
  Submodule.subset_span ⟨b, hb, v, rfl⟩

def contract (l : V →ₗ[R] R) : B ⊗[R] V →ₗ[R] B :=
  (TensorProduct.rid R B).toLinearMap.comp (TensorProduct.map LinearMap.id l)

theorem contract_tmul (l : V →ₗ[R] R) (b : B) (v : V) :
    contract l (b ⊗ₜ[R] v) = l v • b := by
  simp only [contract, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
    LinearEquiv.coe_coe, TensorProduct.rid_tmul]

theorem contract_mem (F : ℤ → Submodule R B) (i : ℤ) (l : V →ₗ[R] R)
    {x : B ⊗[R] V} (hx : x ∈ tensorStep F i) : contract l x ∈ F i := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, v, rfl⟩ := hx
    rw [contract_tmul]
    exact (F i).smul_mem _ hb
  | zero => rw [map_zero]; exact (F i).zero_mem
  | add x y _ _ hx hy => rw [map_add]; exact (F i).add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact (F i).smul_mem a hx

theorem tensorStep_antitone (F : ℤ → Submodule R B) (hF : Antitone F) :
    Antitone (tensorStep F (V := V)) := by
  intro i j hij
  apply Submodule.span_le.mpr
  rintro _ ⟨b, hb, v, rfl⟩
  exact tmul_mem_tensorStep F i (hF hij hb) v

theorem tensorStep_exhaustive (F : ℤ → Submodule R B) (hF : Antitone F)
    (hEx : ∀ b : B, ∃ i : ℤ, b ∈ F i) (x : B ⊗[R] V) :
    ∃ i : ℤ, x ∈ tensorStep F i := by
  induction x using TensorProduct.inductionOn with
  | tmul b v =>
    obtain ⟨i, hi⟩ := hEx b
    exact ⟨i, tmul_mem_tensorStep F i hi v⟩
  | add x y hx hy =>
    obtain ⟨i, hi⟩ := hx
    obtain ⟨j, hj⟩ := hy
    exact ⟨min i j, (tensorStep F (min i j)).add_mem
      (tensorStep_antitone F hF (min_le_left i j) hi)
      (tensorStep_antitone F hF (min_le_right i j) hj)⟩

theorem tensorStep_separated (F : ℤ → Submodule R B)
    (hSep : ∀ b : B, (∀ i : ℤ, b ∈ F i) → b = 0)
    (x : B ⊗[R] V) (hx : ∀ i : ℤ, x ∈ tensorStep F i) : x = 0 := by
  classical
  let b := Module.Basis.ofVectorSpace R V
  apply (TensorProduct.equivFinsuppOfBasisRight b).injective
  rw [map_zero]
  ext j
  have he := hSep (contract (b.coord j) x) (fun i => contract_mem F i (b.coord j) (hx i))
  change TensorProduct.equivFinsuppOfBasisRight b x j = 0
  rw [TensorProduct.equivFinsuppOfBasisRight_apply]
  exact he

variable {S : Type*} [Field S] [Algebra R S] [Module S B]
  [IsScalarTower R S B] [SMulCommClass R S B]

theorem tensorStep_smul_mem (F : ℤ → Submodule S B) (i : ℤ) (a : S)
    {x : B ⊗[R] V} (hx : x ∈ tensorStep (fun j => (F j).restrictScalars R) i) :
    a • x ∈ tensorStep (fun j => (F j).restrictScalars R) i := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, v, rfl⟩ := hx
    rw [TensorProduct.smul_tmul']
    exact tmul_mem_tensorStep (R := R) (fun j => (F j).restrictScalars R) i
      ((F i).smul_mem a hb) v
  | zero => rw [smul_zero]; exact (tensorStep _ i).zero_mem
  | add x y _ _ hx hy => rw [smul_add]; exact (tensorStep _ i).add_mem hx hy
  | smul c x _ hx => rw [smul_comm a c]; exact (tensorStep _ i).smul_mem c hx

def scalarTensorStep (F : ℤ → Submodule S B) (i : ℤ) : Submodule S (B ⊗[R] V) where
  carrier := tensorStep (R := R) (V := V) (fun j => (F j).restrictScalars R) i
  zero_mem' := (tensorStep _ i).zero_mem
  add_mem' := (tensorStep _ i).add_mem
  smul_mem' a _ hx := tensorStep_smul_mem (R := R) F i a hx

end

end OAI.NumberTheory.PadicHodge.WeakAdmissibility.TensorFiltration
