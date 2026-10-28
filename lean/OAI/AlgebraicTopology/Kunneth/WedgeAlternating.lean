import OAI.AlgebraicTopology.Kunneth.CovectorWedge
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Analysis.Calculus.DifferentialForm.Basic

/-! # Wedge Alternating -/

namespace OAI.AlgebraicTopology.Kunneth.WedgeAlternating

noncomputable section

section

/-! Finite alternation identities used for the exterior-product derivative. -/

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Constructions

variable {ι κ E : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

/-- Full, unnormalized alternation, also available for an unbundled function. -/
def alternatingSum (f : (ι → E) → ℂ) (v : ι → E) : ℂ :=
  ∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • f (v ∘ σ)

theorem alternatingSum_add (f g : (ι → E) → ℂ) (v : ι → E) :
    alternatingSum (fun w => f w + g w) v = alternatingSum f v + alternatingSum g v := by
  simp only [alternatingSum, smul_add, Finset.sum_add_distrib]

theorem alternatingSum_smul (c : ℂ) (f : (ι → E) → ℂ) (v : ι → E) :
    alternatingSum (fun w => c * f w) v = c * alternatingSum f v := by
  simp only [alternatingSum, Finset.mul_sum, mul_smul_comm]

theorem alternatingSum_zero (v : ι → E) : alternatingSum (fun _ => (0 : ℂ)) v = 0 := by
  simp only [alternatingSum, smul_zero, Finset.sum_const_zero]

theorem alternatingSum_units_smul (c : ℤˣ) (f : (ι → E) → ℂ) (v : ι → E) :
    alternatingSum (fun w => c • f w) v = c • alternatingSum f v := by
  unfold alternatingSum
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  exact smul_comm _ _ _

theorem alternatingSum_real_smul (c : ℝ) (f : (ι → E) → ℂ) (v : ι → E) :
    alternatingSum (fun w => c • f w) v = c • alternatingSum f v := by
  unfold alternatingSum
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  exact smul_comm _ _ _

/-- Permuting the slots before full alternation changes only the sign. -/
theorem alternatingSum_permute (f : (ι → E) → ℂ) (τ : Equiv.Perm ι) (v : ι → E) :
    alternatingSum (fun w => f (w ∘ τ)) v =
      Equiv.Perm.sign τ • alternatingSum f v := by
  unfold alternatingSum
  rw [Finset.smul_sum]
  apply Fintype.sum_equiv (Equiv.mulRight τ)
  intro σ
  simp only [Equiv.coe_mulRight, Equiv.Perm.coe_mul, Function.comp_assoc,
    map_mul, mul_smul]
  rw [smul_comm (Equiv.Perm.sign τ) (Equiv.Perm.sign σ),
    ← mul_smul (Equiv.Perm.sign τ) (Equiv.Perm.sign τ),
    Int.units_mul_self, one_smul]

/-- Alternating a family of alternating covectors counts each permutation equally. -/
theorem alternatingSum_of_alternating
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E [⋀^ι]→L[ℝ] ℂ) (v : ι → E) :
    alternatingSum a v = (Fintype.card ι).factorial • a v := by
  have hp (σ : Equiv.Perm ι) : a (v ∘ σ) = Equiv.Perm.sign σ • a v :=
    a.toAlternatingMap.map_perm v σ
  simp only [alternatingSum, hp, ← mul_smul, Int.units_mul_self, one_smul,
    Finset.sum_const, Finset.card_univ, Fintype.card_perm]

/-- Alternation is invariant under a change of the finite index type. -/
theorem alternatingSum_reindex (e : ι ≃ κ) (f : (ι → E) → ℂ) (v : κ → E) :
    alternatingSum (fun w => f (w ∘ e)) v = alternatingSum f (v ∘ e) := by
  unfold alternatingSum
  apply Fintype.sum_equiv (Equiv.permCongr e.symm)
  intro σ
  simp only [Equiv.Perm.sign_permCongr]
  congr 1
  congr 1
  ext i
  simp

/-- A scalar-valued product on two disjoint blocks of slots. -/
def blockProduct (f : (ι → E) → ℂ) (g : (κ → E) → ℂ) (v : ι ⊕ κ → E) : ℂ :=
  f (v ∘ Sum.inl) * g (v ∘ Sum.inr)

theorem alternatingSum_block_left (f : (ι → E) → ℂ) (g : (κ → E) → ℂ)
    (v : ι ⊕ κ → E) :
    alternatingSum (blockProduct (alternatingSum f) g) v =
      (Fintype.card ι).factorial • alternatingSum (blockProduct f g) v := by
  classical
  have hterm (τ : Equiv.Perm ι) :
      alternatingSum (fun w => Equiv.Perm.sign τ •
        blockProduct f g (w ∘ Equiv.sumCongr τ (Equiv.refl κ))) v =
          alternatingSum (blockProduct f g) v := by
    rw [alternatingSum_units_smul, alternatingSum_permute, ← mul_smul]
    simp only [Equiv.Perm.sign_sumCongr, Equiv.Perm.sign_refl, mul_one,
      Int.units_mul_self, one_smul]
  calc
    alternatingSum (blockProduct (alternatingSum f) g) v =
        ∑ τ : Equiv.Perm ι, alternatingSum (fun w => Equiv.Perm.sign τ •
          blockProduct f g (w ∘ Equiv.sumCongr τ (Equiv.refl κ))) v := by
      simp only [alternatingSum, blockProduct, Finset.sum_mul, smul_mul_assoc,
        Finset.smul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro τ _
      apply Finset.sum_congr rfl
      intro σ _
      congr 2
    _ = _ := by
      simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_perm]

theorem alternatingSum_block_right (f : (ι → E) → ℂ) (g : (κ → E) → ℂ)
    (v : ι ⊕ κ → E) :
    alternatingSum (blockProduct f (alternatingSum g)) v =
      (Fintype.card κ).factorial • alternatingSum (blockProduct f g) v := by
  classical
  have hterm (τ : Equiv.Perm κ) :
      alternatingSum (fun w => Equiv.Perm.sign τ •
        blockProduct f g (w ∘ Equiv.sumCongr (Equiv.refl ι) τ)) v =
          alternatingSum (blockProduct f g) v := by
    rw [alternatingSum_units_smul, alternatingSum_permute, ← mul_smul]
    simp only [Equiv.Perm.sign_sumCongr, Equiv.Perm.sign_refl, one_mul,
      Int.units_mul_self, one_smul]
  calc
    alternatingSum (blockProduct f (alternatingSum g)) v =
        ∑ τ : Equiv.Perm κ, alternatingSum (fun w => Equiv.Perm.sign τ •
          blockProduct f g (w ∘ Equiv.sumCongr (Equiv.refl ι) τ)) v := by
      simp only [alternatingSum, blockProduct, Finset.mul_sum, mul_smul_comm,
        Finset.smul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro τ _
      apply Finset.sum_congr rfl
      intro σ _
      congr 2
    _ = _ := by
      simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_perm]

theorem alternatingSum_block_left_zero (f : (ι → E) → ℂ) (g : (κ → E) → ℂ)
    (hf : ∀ w, alternatingSum f w = 0) (v : ι ⊕ κ → E) :
    alternatingSum (blockProduct f g) v = 0 := by
  have h := (alternatingSum_block_left f g v).symm
  have hz : blockProduct (alternatingSum f) g = fun _ => (0 : ℂ) := by
    funext w
    simp only [blockProduct, hf, zero_mul]
  rw [hz, alternatingSum_zero, nsmul_eq_mul] at h
  exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast Nat.factorial_ne_zero _)

theorem alternatingSum_block_right_zero (f : (ι → E) → ℂ) (g : (κ → E) → ℂ)
    (hg : ∀ w, alternatingSum g w = 0) (v : ι ⊕ κ → E) :
    alternatingSum (blockProduct f g) v = 0 := by
  have h := (alternatingSum_block_right f g v).symm
  have hz : blockProduct f (alternatingSum g) = fun _ => (0 : ℂ) := by
    funext w
    simp only [blockProduct, hg, mul_zero]
  rw [hz, alternatingSum_zero, nsmul_eq_mul] at h
  exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast Nat.factorial_ne_zero _)

/-- Alternating in all but the first slot before full alternation only rescales it. -/
theorem alternatingSum_tail {n : ℕ} (f : E → (Fin n → E) → ℂ)
    (v : Fin (n + 1) → E) :
    alternatingSum (fun w => alternatingSum (f (w 0)) (Fin.tail w)) v =
      n.factorial • alternatingSum (fun w => f (w 0) (Fin.tail w)) v := by
  have hterm (τ : Equiv.Perm (Fin n)) :
      alternatingSum (fun w => Equiv.Perm.sign τ •
        f (w 0) (Fin.tail w ∘ τ)) v =
          alternatingSum (fun w => f (w 0) (Fin.tail w)) v := by
    have he : (fun w : Fin (n + 1) → E => f (w 0) (Fin.tail w ∘ τ)) =
        (fun w => (fun u => f (u 0) (Fin.tail u))
          (w ∘ Equiv.Perm.decomposeFin.symm (0, τ))) := by
      funext w
      simp only [Function.comp_apply, Equiv.Perm.decomposeFin_symm_apply_zero]
      rfl
    rw [alternatingSum_units_smul, he]
    rw [alternatingSum_permute (fun w => f (w 0) (Fin.tail w))
      (Equiv.Perm.decomposeFin.symm (0, τ)), ← mul_smul]
    simp only [Equiv.Perm.decomposeFin.symm_sign, ite_true, one_mul,
      Int.units_mul_self, one_smul]
  calc
    alternatingSum (fun w => alternatingSum (f (w 0)) (Fin.tail w)) v =
        ∑ τ : Equiv.Perm (Fin n), alternatingSum (fun w => Equiv.Perm.sign τ •
          f (w 0) (Fin.tail w ∘ τ)) v := by
      simp only [alternatingSum, Finset.smul_sum]
      rw [Finset.sum_comm]
    _ = _ := by
      simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
        Fintype.card_fin]

/-- Full alternation of a linear slot followed by alternating slots is the
usual exterior-derivative sum times the factorial of the latter degree. -/
theorem alternatingSum_firstTail {n : ℕ}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E [⋀^Fin n]→L[ℝ] ℂ) (v : Fin (n + 1) → E) :
    alternatingSum (fun w => f (w 0) (Fin.tail w)) v =
      n.factorial • ∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val • f (v i) (i.removeNth v) := by
  have hterm (i : Fin (n + 1)) (σ : Equiv.Perm (Fin n)) :
      Equiv.Perm.sign (Equiv.Perm.decomposeFin.symm (i, σ)) •
        f (v i) (Fin.tail (v ∘ Equiv.Perm.decomposeFin.symm (i, σ))) =
      (-1 : ℤ) ^ i.val • f (v i) (i.removeNth v) := by
    cases i using Fin.cases with
    | zero =>
      have hv : Fin.tail (v ∘ Equiv.Perm.decomposeFin.symm (0, σ)) =
          Fin.tail v ∘ σ := by
        funext j
        simp only [Fin.tail, Function.comp_apply,
          Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self,
          Equiv.coe_refl, id_eq]
      rw [hv]
      change Equiv.Perm.sign _ • (f (v 0)).toAlternatingMap (Fin.tail v ∘ σ) = _
      rw [AlternatingMap.map_perm]
      simp only [Equiv.Perm.decomposeFin.symm_sign, ite_true, one_mul,
        ← mul_smul, Int.units_mul_self, one_smul, Fin.val_zero, pow_zero,
        Fin.removeNth_zero]
      rfl
    | succ i =>
      have hv : Fin.tail (v ∘ Equiv.Perm.decomposeFin.symm (i.succ, σ)) =
          (i.succ.removeNth v ∘ i.cycleRange) ∘ σ := by
        funext j
        simp only [Fin.tail, Function.comp_apply,
          Equiv.Perm.decomposeFin_symm_apply_succ, Fin.removeNth_apply,
          Fin.succAbove_cycleRange]
      rw [hv]
      change Equiv.Perm.sign _ • (f (v i.succ)).toAlternatingMap
        ((i.succ.removeNth v ∘ i.cycleRange) ∘ σ) = _
      rw [AlternatingMap.map_perm, AlternatingMap.map_perm]
      rw [Equiv.Perm.decomposeFin.symm_sign, ite_eq_right (Fin.succ_ne_zero i),
        mul_smul, ← mul_smul (Equiv.Perm.sign σ) (Equiv.Perm.sign σ),
        Int.units_mul_self, one_smul, Fin.sign_cycleRange]
      simp only [Fin.val_succ, pow_succ', mul_smul, Units.smul_def,
        Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
      rfl
  unfold alternatingSum
  rw [Finset.univ_perm_fin_succ, ← Finset.univ_product_univ]
  simp only [Finset.sum_map, Equiv.toEmbedding_apply, Finset.sum_product,
    Function.comp_apply, Equiv.Perm.decomposeFin_symm_apply_zero, hterm,
    Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    Finset.smul_sum]

end Constructions

end

section

/-! The exterior derivative of the standard covector product. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators

namespace Constructions

variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D] {p q : ℕ}

/-- Differentiate the finite alternating product coefficient by coefficient. -/
theorem covectorWedge_fderiv_apply {a : D → E [⋀^Fin p]→L[ℝ] ℂ}
    {b : D → E [⋀^Fin q]→L[ℝ] ℂ} {x : D}
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x)
    (u : D) (v : Fin (p + q) → E) :
    fderiv ℝ (fun y => CovectorWedge.Constructions.covectorWedge (a y) (b y) v) x u =
      (((p.factorial : ℝ) * (q.factorial : ℝ))⁻¹) •
        alternatingSum (fun w =>
          (fderiv ℝ a x u) (fun i => w (Fin.castAdd q i)) *
            b x (fun i => w (Fin.natAdd p i)) +
          a x (fun i => w (Fin.castAdd q i)) *
            (fderiv ℝ b x u) (fun i => w (Fin.natAdd p i))) v := by
  let left (σ : Equiv.Perm (Fin (p + q))) : Fin p → E :=
    fun i => v (σ (Fin.castAdd q i))
  let right (σ : Equiv.Perm (Fin (p + q))) : Fin q → E :=
    fun i => v (σ (Fin.natAdd p i))
  have hσ (σ : Equiv.Perm (Fin (p + q))) :=
    ((ha.hasFDerivAt.continuousAlternatingMap_apply_const (left σ)).mul
      (hb.hasFDerivAt.continuousAlternatingMap_apply_const (right σ))).const_smul
        (Equiv.Perm.sign σ)
  have ht := (HasFDerivAt.fun_sum (u := Finset.univ) (fun σ _ => hσ σ)).const_smul
    (((p.factorial : ℝ) * (q.factorial : ℝ))⁻¹)
  simp only [Pi.smul_apply, Pi.mul_apply] at ht
  have he : (fun y => CovectorWedge.Constructions.covectorWedge (a y) (b y) v) =
      (fun y => (((p.factorial : ℝ) * (q.factorial : ℝ))⁻¹) •
        ∑ σ : Equiv.Perm (Fin (p + q)), Equiv.Perm.sign σ •
          (a y (left σ) * b y (right σ))) := by
    funext y
    exact CovectorWedge.Constructions.covectorWedge_apply (a y) (b y) v
  rw [he]
  erw [ht.fderiv]
  simp only [smul_apply, sum_apply, add_apply,
    smul_eq_mul, alternatingSum]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  change a x (left σ) * (fderiv ℝ b x u) (right σ) +
    b x (right σ) * (fderiv ℝ a x u) (left σ) = _
  dsimp only [left, right, Function.comp_apply]
  ring

/-- Exterior differentiation is full alternation of its ordinary derivative,
with the expected factorial. -/
theorem alternatingSum_fderiv {n : ℕ} (a : E → E [⋀^Fin n]→L[ℝ] ℂ)
    (x : E) (v : Fin (n + 1) → E) :
    alternatingSum (fun w => (fderiv ℝ a x) (w 0) (Fin.tail w)) v =
      n.factorial • extDeriv a x v := by
  rw [alternatingSum_firstTail]
  simp only [extDeriv, ContinuousAlternatingMap.alternatizeUncurryFin_apply]

end Constructions

end

/-! Products of closed differential forms are closed. -/

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Constructions

def leftDerivativeIndex (p q : ℕ) : Fin (p + 1) ⊕ Fin q ≃ Fin (p + q + 1) :=
  finSumFinEquiv.trans (finCongr (by omega))

@[simp] theorem leftDerivativeIndex_zero (p q : ℕ) :
    leftDerivativeIndex p q (Sum.inl 0) = 0 := rfl

@[simp] theorem leftDerivativeIndex_left (p q : ℕ) (i : Fin p) :
    leftDerivativeIndex p q (Sum.inl i.succ) = (Fin.castAdd q i).succ := rfl

@[simp] theorem leftDerivativeIndex_right (p q : ℕ) (i : Fin q) :
    leftDerivativeIndex p q (Sum.inr i) = (Fin.natAdd p i).succ := by
  apply Fin.ext
  simp only [leftDerivativeIndex, Equiv.trans_apply, finSumFinEquiv_apply_right,
    finCongr_apply, Fin.val_cast, Fin.val_natAdd, Fin.val_succ]
  omega

def rightDerivativeIndex (p q : ℕ) : Fin p ⊕ Fin (q + 1) ≃ Fin (p + q + 1) :=
  (finSumFinEquiv.trans (finCongr (by omega))).trans
    (Fin.cycleRange ⟨p, by omega⟩)

@[simp] theorem rightDerivativeIndex_left (p q : ℕ) (i : Fin p) :
    rightDerivativeIndex p q (Sum.inl i) = (Fin.castAdd q i).succ := by
  apply Fin.ext
  change (Fin.cycleRange (⟨p, by omega⟩ : Fin (p + q + 1))
    (Fin.cast (by omega) (Fin.castAdd (q + 1) i))).val = i.val + 1
  rw [Fin.coe_cycleRange_of_lt (show Fin.cast (by omega) (Fin.castAdd (q + 1) i) <
    (⟨p, by omega⟩ : Fin (p + q + 1)) from i.isLt)]
  rfl

@[simp] theorem rightDerivativeIndex_zero (p q : ℕ) :
    rightDerivativeIndex p q (Sum.inr 0) = 0 := by
  change Fin.cycleRange (⟨p, by omega⟩ : Fin (p + q + 1))
    (Fin.cast (by omega) (Fin.natAdd p (0 : Fin (q + 1)))) = 0
  have he : Fin.cast (by omega) (Fin.natAdd p (0 : Fin (q + 1))) =
      (⟨p, by omega⟩ : Fin (p + q + 1)) := by apply Fin.ext; simp
  rw [he, Fin.cycleRange_self]

@[simp] theorem rightDerivativeIndex_right (p q : ℕ) (i : Fin q) :
    rightDerivativeIndex p q (Sum.inr i.succ) = (Fin.natAdd p i).succ := by
  change Fin.cycleRange (⟨p, by omega⟩ : Fin (p + q + 1))
    (Fin.cast (by omega) (Fin.natAdd p i.succ)) = _
  rw [Fin.cycleRange_of_gt (show (⟨p, by omega⟩ : Fin (p + q + 1)) <
    Fin.cast (by omega) (Fin.natAdd p i.succ) from by
      change p < p + (i.val + 1)
      omega)]
  apply Fin.ext
  simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_succ]
  omega

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {p q : ℕ}

theorem alternatingSum_derivative_left_zero
    (a : E → E [⋀^Fin p]→L[ℝ] ℂ) (b : E [⋀^Fin q]→L[ℝ] ℂ)
    (x : E) (ha : extDeriv a x = 0) (v : Fin (p + q + 1) → E) :
    alternatingSum (fun w =>
      (fderiv ℝ a x) (w 0) (fun i => w (Fin.castAdd q i).succ) *
        b (fun i => w (Fin.natAdd p i).succ)) v = 0 := by
  let f : (Fin (p + 1) → E) → ℂ := fun w => (fderiv ℝ a x) (w 0) (Fin.tail w)
  have hf (w : Fin (p + 1) → E) : alternatingSum f w = 0 := by
    change alternatingSum (fun u => (fderiv ℝ a x) (u 0) (Fin.tail u)) w = 0
    rw [alternatingSum_fderiv, ha]
    exact smul_zero _
  have hz := alternatingSum_block_left_zero f b hf (v ∘ leftDerivativeIndex p q)
  have hr := alternatingSum_reindex (leftDerivativeIndex p q) (blockProduct f b) v
  rw [hz] at hr
  convert hr using 1
  congr 1
  funext w
  change _ = (fderiv ℝ a x) (w (leftDerivativeIndex p q (Sum.inl 0)))
    (fun i => w (leftDerivativeIndex p q (Sum.inl i.succ))) *
      b (fun i => w (leftDerivativeIndex p q (Sum.inr i)))
  simp only [leftDerivativeIndex_zero, leftDerivativeIndex_left, leftDerivativeIndex_right]

theorem alternatingSum_derivative_right_zero
    (a : E [⋀^Fin p]→L[ℝ] ℂ) (b : E → E [⋀^Fin q]→L[ℝ] ℂ)
    (x : E) (hb : extDeriv b x = 0) (v : Fin (p + q + 1) → E) :
    alternatingSum (fun w =>
      a (fun i => w (Fin.castAdd q i).succ) *
        (fderiv ℝ b x) (w 0) (fun i => w (Fin.natAdd p i).succ)) v = 0 := by
  let g : (Fin (q + 1) → E) → ℂ := fun w => (fderiv ℝ b x) (w 0) (Fin.tail w)
  have hg (w : Fin (q + 1) → E) : alternatingSum g w = 0 := by
    change alternatingSum (fun u => (fderiv ℝ b x) (u 0) (Fin.tail u)) w = 0
    rw [alternatingSum_fderiv, hb]
    exact smul_zero _
  have hz := alternatingSum_block_right_zero a g hg (v ∘ rightDerivativeIndex p q)
  have hr := alternatingSum_reindex (rightDerivativeIndex p q) (blockProduct a g) v
  rw [hz] at hr
  convert hr using 1
  congr 1
  funext w
  change _ = a (fun i => w (rightDerivativeIndex p q (Sum.inl i))) *
    (fderiv ℝ b x) (w (rightDerivativeIndex p q (Sum.inr 0)))
      (fun i => w (rightDerivativeIndex p q (Sum.inr i.succ)))
  simp only [rightDerivativeIndex_zero, rightDerivativeIndex_left, rightDerivativeIndex_right]

/-- Exterior multiplication preserves the actual exterior-derivative kernel. -/
theorem extDeriv_covectorWedge_eq_zero
    (a : E → E [⋀^Fin p]→L[ℝ] ℂ) (b : E → E [⋀^Fin q]→L[ℝ] ℂ) (x : E)
    (ha : ContDiffAt ℝ 1 a x) (hb : ContDiffAt ℝ 1 b x)
    (hda : extDeriv a x = 0) (hdb : extDeriv b x = 0) :
    extDeriv (fun y => CovectorWedge.Constructions.covectorWedge (a y) (b y)) x = 0 := by
  let c : ℝ := ((p.factorial : ℝ) * (q.factorial : ℝ))⁻¹
  let F : E → (Fin (p + q) → E) → ℂ := fun u w =>
    (fderiv ℝ a x u) (fun i => w (Fin.castAdd q i)) *
      b x (fun i => w (Fin.natAdd p i)) +
    a x (fun i => w (Fin.castAdd q i)) *
      (fderiv ℝ b x u) (fun i => w (Fin.natAdd p i))
  have had : DifferentiableAt ℝ a x := ha.differentiableAt (by simp)
  have hbd : DifferentiableAt ℝ b x := hb.differentiableAt (by simp)
  have hwd : DifferentiableAt ℝ (fun y => CovectorWedge.Constructions.covectorWedge (a y) (b y)) x :=
    (CovectorWedge.Constructions.contDiffAt_covectorWedge ha hb).differentiableAt (by simp)
  have hd (u : E) (v : Fin (p + q) → E) :
      (fderiv ℝ (fun y => CovectorWedge.Constructions.covectorWedge (a y) (b y)) x u) v =
        c • alternatingSum (F u) v := by
    rw [← fderiv_continuousAlternatingMap_apply_const_apply hwd]
    exact covectorWedge_fderiv_apply had hbd u v
  ext v
  have hz : (p + q).factorial •
      extDeriv (fun y => CovectorWedge.Constructions.covectorWedge (a y) (b y)) x v = 0 := by
    rw [← alternatingSum_fderiv]
    simp_rw [hd]
    rw [alternatingSum_real_smul, alternatingSum_tail]
    have hF : alternatingSum (fun w => F (w 0) (Fin.tail w)) v = 0 := by
      change alternatingSum (fun w =>
        (fderiv ℝ a x) (w 0) (fun i => w (Fin.castAdd q i).succ) *
          b x (fun i => w (Fin.natAdd p i).succ) +
        a x (fun i => w (Fin.castAdd q i).succ) *
          (fderiv ℝ b x) (w 0) (fun i => w (Fin.natAdd p i).succ)) v = 0
      rw [alternatingSum_add, alternatingSum_derivative_left_zero a (b x) x hda,
        alternatingSum_derivative_right_zero (a x) b x hdb, add_zero]
    rw [hF, smul_zero, smul_zero]
  rw [nsmul_eq_mul] at hz
  exact (mul_eq_zero.mp hz).resolve_left (by exact_mod_cast Nat.factorial_ne_zero _)

end Constructions

end

end OAI.AlgebraicTopology.Kunneth.WedgeAlternating
