import OAI.Analysis.HodgeTheory.Decomposition.Multilinear
import OAI.AlgebraicGeometry.ComplexMultiplication.SignSwitch
import Mathlib.LinearAlgebra.Alternating.Basic

/-! # Pointwise -/

namespace OAI.Analysis.HodgeTheory.Decomposition.Pointwise.Constructions

noncomputable section

/-! Pure-character spanning for actual algebraic alternating covectors. -/

open scoped BigOperators

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E]

/-- A signed joint eigenvector is complex-linear or conjugate-linear in each slot. -/
theorem signed_slot_scalar (n : ℕ) (ε : Fin n → Bool) (f : Multilinear.Constructions.RealMultilinear E n)
    (hf : f ∈ Multilinear.Constructions.signedMultilinearSpace E n ε) (i : Fin n) (z : ℂ) (v : Fin n → E) :
    f (Function.update v i (z • v i)) = (if ε i then z else star z) * f v := by
  have hi := (iInf_le (fun j => (Multilinear.Constructions.slotRotation E n j).eigenspace
    (if ε j then Complex.I else -Complex.I)) i) hf
  rw [Module.End.mem_eigenspace_iff] at hi
  have hJ := congrArg (fun g : Multilinear.Constructions.RealMultilinear E n => g v) hi
  rw [Multilinear.Constructions.slotRotation_apply] at hJ
  change f (Function.update v i (Complex.I • v i)) =
    (if ε i then Complex.I else -Complex.I) * f v at hJ
  have hR (r : ℝ) (x : E) : (r : ℂ) • x = r • x := algebraMap_smul ℂ r x
  have hz : z • v i = z.re • v i + z.im • (Complex.I • v i) := by
    conv_lhs => rw [← Complex.re_add_im z]
    rw [add_smul, mul_smul, hR, hR]
  have hc : (z.re : ℂ) + (z.im : ℂ) * (if ε i then Complex.I else -Complex.I) =
      (if ε i then z else star z) := by
    cases ε i <;> apply Complex.ext <;> simp
  rw [hz, f.map_update_add, f.map_update_smul, f.map_update_smul,
    Function.update_eq_self, hJ]
  simp only [Complex.real_smul]
  calc
    (z.re : ℂ) * f v + (z.im : ℂ) * ((if ε i then Complex.I else -Complex.I) * f v) =
        ((z.re : ℂ) + (z.im : ℂ) * (if ε i then Complex.I else -Complex.I)) * f v := by ring
    _ = _ := by rw [hc]

section SlotProduct

variable {ι A : Type*} [Fintype ι] [DecidableEq ι]

/-- Independent transformations of all slots multiply their individual eigenvalues. -/
theorem apply_all_slots (f : (ι → A) → ℂ) (L : ι → A → A) (c : ι → ℂ)
    (h : ∀ i v, f (Function.update v i (L i (v i))) = c i * f v)
    (v : ι → A) : f (fun i => L i (v i)) = (∏ i, c i) * f v := by
  have aux (s : Finset ι) :
      f (fun i => if i ∈ s then L i (v i) else v i) = (∏ i ∈ s, c i) * f v := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s his ih =>
      let w : ι → A := fun j => if j ∈ s then L j (v j) else v j
      have hw : (fun j => if j ∈ insert i s then L j (v j) else v j) =
          Function.update w i (L i (w i)) := by
        funext j
        by_cases hji : j = i
        · subst j
          simp [w, his]
        · simp [w, hji]
      rw [hw, h]
      change c i * f (fun j => if j ∈ s then L j (v j) else v j) = _
      rw [ih, Finset.prod_insert his, mul_assoc]
  simpa using aux Finset.univ

end SlotProduct

def signBidegree {n : ℕ} (ε : Fin n → Bool) : Core.Constructions.Bidegree n :=
  ⟨(Fintype.card {i // ε i = true}, Fintype.card {i // ε i = false}), by
    simpa only [AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signCount, Fintype.card_fin] using
      AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signCount_true_add_false (fun i (_ : Unit) => ε i) ()⟩

theorem signed_product_character {n : ℕ} (ε : Fin n → Bool) (z : ℂˣ) :
    (∏ i, if ε i then (z : ℂ) else star (z : ℂ)) =
      DifferentialForms.Manifold.Bidegree.bidegreeCharacter (signBidegree ε).val.1 (signBidegree ε).val.2 z := by
  classical
  simp only [signBidegree, Finset.prod_ite, Finset.prod_const,
    DifferentialForms.Manifold.Bidegree.bidegreeCharacter, Fintype.card_subtype, Bool.not_eq_true]

/-- The simultaneous scalar character depends only on the numbers of the two slot types. -/
theorem signed_multilinear_character (n : ℕ) (ε : Fin n → Bool) (f : Multilinear.Constructions.RealMultilinear E n)
    (hf : f ∈ Multilinear.Constructions.signedMultilinearSpace E n ε) (z : ℂˣ) (v : Fin n → E) :
    f (fun i => (z : ℂ) • v i) =
      DifferentialForms.Manifold.Bidegree.bidegreeCharacter (signBidegree ε).val.1 (signBidegree ε).val.2 z * f v := by
  rw [apply_all_slots f (fun _ x => (z : ℂ) • x)
    (fun i => if ε i then (z : ℂ) else star (z : ℂ))
    (fun i v => signed_slot_scalar E n ε f hf i z v) v,
    signed_product_character]

/-- The complex-linear alternatization map on the actual multilinear covectors. -/
def alternatizationLinear (n : ℕ) :
    Multilinear.Constructions.RealMultilinear E n →ₗ[ℂ] (E [⋀^Fin n]→ₗ[ℝ] ℂ) where
  toFun := MultilinearMap.alternatization
  map_add' := MultilinearMap.alternatization.map_add
  map_smul' c f := by
    ext v
    simp only [RingHom.id_apply, AlternatingMap.smul_apply,
      MultilinearMap.alternatization_apply, MultilinearMap.domDomCongr_apply,
      smul_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    exact smul_comm (Equiv.Perm.sign σ) c _

/-- Algebraic pure covectors in one fixed total degree. -/
def algebraicPureSpace (n : ℕ) (i : Core.Constructions.Bidegree n) :
    Submodule ℂ (E [⋀^Fin n]→ₗ[ℝ] ℂ) where
  carrier := {f | ∀ z : ℂˣ, ∀ v, f (fun j => (z : ℂ) • v j) =
    DifferentialForms.Manifold.Bidegree.bidegreeCharacter i.val.1 i.val.2 z * f v}
  zero_mem' := by intro z v; simp
  add_mem' := by
    intro f g hf hg z v
    simpa only [AlternatingMap.add_apply, mul_add] using congrArg₂ (· + ·) (hf z v) (hg z v)
  smul_mem' := by
    intro c f hf z v
    change c * f (fun j => (z : ℂ) • v j) = DifferentialForms.Manifold.Bidegree.bidegreeCharacter i.val.1 i.val.2 z * (c * f v)
    rw [hf]
    ring

/-- Alternatization preserves the scalar character. -/
theorem alternatization_signed_mem (n : ℕ) (ε : Fin n → Bool) (f : Multilinear.Constructions.RealMultilinear E n)
    (hf : f ∈ Multilinear.Constructions.signedMultilinearSpace E n ε) :
    alternatizationLinear E n f ∈ algebraicPureSpace E n (signBidegree ε) := by
  intro z v
  simp only [alternatizationLinear, LinearMap.coe_mk, AddHom.coe_mk,
    MultilinearMap.alternatization_apply, MultilinearMap.domDomCongr_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [signed_multilinear_character E n ε f hf z (fun j => v (σ j))]
  exact (smul_comm (Equiv.Perm.sign σ)
    (DifferentialForms.Manifold.Bidegree.bidegreeCharacter (signBidegree ε).val.1 (signBidegree ε).val.2 z) (f (fun j => v (σ j))))

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
/-- Alternatization is onto in characteristic zero. -/
theorem alternatizationLinear_surjective (n : ℕ) : Function.Surjective (alternatizationLinear E n) := by
  intro f
  refine ⟨((n.factorial : ℂ)⁻¹) • f.toMultilinearMap, ?_⟩
  rw [map_smul]
  change ((n.factorial : ℂ)⁻¹) • MultilinearMap.alternatization f.toMultilinearMap = f
  rw [AlternatingMap.coe_alternatization, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℂ n.factorial f, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)), one_smul]

/-- Every algebraic alternating covector is a sum of covectors of pure bidegree. -/
theorem algebraicPureSpace_span [FiniteDimensional ℝ E] (n : ℕ) :
    (⨆ i : Core.Constructions.Bidegree n, algebraicPureSpace E n i) = ⊤ := by
  apply top_unique
  have htop : (⊤ : Submodule ℂ (E [⋀^Fin n]→ₗ[ℝ] ℂ)) =
      (⊤ : Submodule ℂ (Multilinear.Constructions.RealMultilinear E n)).map (alternatizationLinear E n) := by
    rw [Submodule.map_top, LinearMap.range_eq_top.mpr (alternatizationLinear_surjective E n)]
  rw [htop, ← Multilinear.Constructions.signedMultilinearSpace_span E n, Submodule.map_iSup]
  refine iSup_le fun ε => ?_
  apply le_trans _ (le_iSup (algebraicPureSpace E n) (signBidegree ε))
  rintro _ ⟨f, hf, rfl⟩
  exact alternatization_signed_mem E n ε f hf

end

end OAI.Analysis.HodgeTheory.Decomposition.Pointwise.Constructions
