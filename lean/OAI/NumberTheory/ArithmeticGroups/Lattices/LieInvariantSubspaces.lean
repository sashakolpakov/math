import OAI.NumberTheory.ArithmeticGroups.Lattices.StabilizerRestriction

/-! # Lie Invariant Subspaces -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.LieInvariantSubspaces.Construction

noncomputable section

section

/-! A faithful linear group is solvable if its actions on an invariant
subspace and the corresponding quotient both have solvable images. -/

open scoped Classical

variable {R V H : Type*} [CommRing R] [AddCommGroup V] [Module R V] [Group H]

def invariantRestriction (ρ : H →* (V ≃ₗ[R] V)) (W : Submodule R V)
    (hW : ∀ g, W.map (ρ g).toLinearMap = W) : H →* (W ≃ₗ[R] W) where
  toFun g := (ρ g).ofSubmodules W W (hW g)
  map_one' := by
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    change ρ 1 x.val = x.val
    rw [map_one]
    rfl
  map_mul' g h := by
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    change ρ (g * h) x.val = ρ g (ρ h x.val)
    rw [map_mul]
    rfl

def invariantQuotient (ρ : H →* (V ≃ₗ[R] V)) (W : Submodule R V)
    (hW : ∀ g, W.map (ρ g).toLinearMap = W) : H →* ((V ⧸ W) ≃ₗ[R] (V ⧸ W)) where
  toFun g := Submodule.Quotient.equiv W W (ρ g) (hW g)
  map_one' := by
    apply LinearEquiv.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H x => simp
  map_mul' g h := by
    apply LinearEquiv.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H x => simp

theorem linearEquiv_commute_of_trivial_subquotient
    (W : Submodule R V) (e f : V ≃ₗ[R] V)
    (heW : ∀ x ∈ W, e x = x) (hfW : ∀ x ∈ W, f x = x)
    (heQ : ∀ x, e x - x ∈ W) (hfQ : ∀ x, f x - x ∈ W) : e * f = f * e := by
  apply LinearEquiv.ext
  intro x
  have he := heW (f x - x) (hfQ x)
  have hf := hfW (e x - x) (heQ x)
  rw [map_sub] at he hf
  change e (f x) = f (e x)
  apply add_right_cancel (b := x)
  calc
    e (f x) + x = f x + e x := sub_eq_sub_iff_add_eq_add.mp he
    _ = e x + f x := add_comm _ _
    _ = f (e x) + x := (sub_eq_sub_iff_add_eq_add.mp hf).symm

theorem linear_group_solvable_of_subquotient
    (ρ : H →* (V ≃ₗ[R] V)) (hρ : Function.Injective ρ)
    (W : Submodule R V) (hW : ∀ g, W.map (ρ g).toLinearMap = W)
    [Group.IsSolvable (invariantRestriction ρ W hW).range]
    [Group.IsSolvable (invariantQuotient ρ W hW).range] : Group.IsSolvable H := by
  let r := invariantRestriction ρ W hW
  let q := invariantQuotient ρ W hW
  let f := r.rangeRestrict.prod q.rangeRestrict
  have hker : Group.IsSolvable f.ker := by
    apply Group.isSolvable_of_comm
    intro a b
    apply Subtype.ext
    apply hρ
    change ρ (a.val * b.val) = ρ (b.val * a.val)
    rw [map_mul, map_mul]
    have hr (g : f.ker) : r g.val = 1 := by
      have he := congrArg (fun z : r.range × q.range => z.1.val) g.property
      exact he
    have hq (g : f.ker) : q g.val = 1 := by
      have he := congrArg (fun z : r.range × q.range => z.2.val) g.property
      exact he
    have hfix (g : f.ker) (x : V) (hx : x ∈ W) : ρ g.val x = x := by
      exact congrArg (fun e : W ≃ₗ[R] W => (e ⟨x, hx⟩).val) (hr g)
    have hdiff (g : f.ker) (x : V) : ρ g.val x - x ∈ W := by
      have he := congrArg (fun e : (V ⧸ W) ≃ₗ[R] (V ⧸ W) => e (Submodule.Quotient.mk x)) (hq g)
      exact (Submodule.Quotient.eq W).mp he
    exact linearEquiv_commute_of_trivial_subquotient W (ρ a.val) (ρ b.val)
      (hfix a) (hfix b) (hdiff a) (hdiff b)
  let : Group.IsSolvable f.ker := hker
  exact Group.isSolvable_of_ker_le_range f.ker.subtype f
    (by rw [Subgroup.range_subtype])

end

/-! Common invariant lines for solvable Lie modules, and descent of
subspace invariance to quotient representations. -/

open scoped Classical
open Set

theorem exists_lie_invariant_line
    {k L V : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    [LieRing L] [LieAlgebra k L] [LieAlgebra.IsSolvable L]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V]
    [LieRingModule L V] [LieModule k L V] :
    ∃ W : LieSubmodule k L V, Module.finrank k W = 1 := by
  obtain ⟨χ, hχ⟩ := LieModule.exists_nontrivial_weightSpace_of_isSolvable k L V
  let : Nontrivial (LieModule.weightSpace V χ) := hχ
  obtain ⟨v, hv⟩ := exists_ne (0 : LieModule.weightSpace V χ)
  have hv0 : (v : V) ≠ 0 := by simpa only [ne_eq, Subtype.ext_iff, ZeroMemClass.coe_zero] using hv
  have heig : ∀ a : L, ⁅a, (v : V)⁆ = χ a • (v : V) :=
    (LieModule.mem_weightSpace χ v.val).mp v.property
  let W : LieSubmodule k L V :=
    { toSubmodule := Submodule.span k {v.val}
      lie_mem := by
        intro a x hx
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
        rw [lie_smul, heig]
        exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span (mem_singleton _))) }
  exact ⟨W, finrank_span_singleton hv0⟩

theorem invariant_map_eq_of_mem
    {k V H : Type*} [Field k] [AddCommGroup V] [Module k V] [Group H]
    (ρ : H →* (V ≃ₗ[k] V)) (W : Submodule k V)
    (hW : ∀ g x, x ∈ W → ρ g x ∈ W) (g : H) : W.map (ρ g).toLinearMap = W := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact hW g x hx
  · intro x hx
    refine ⟨ρ g⁻¹ x, hW g⁻¹ x hx, ?_⟩
    change ρ g (ρ g⁻¹ x) = x
    have he := congrArg (fun e : V ≃ₗ[k] V => e x) (ρ.map_mul g g⁻¹)
    simpa only [mul_inv_cancel, map_one, LinearEquiv.coe_one, id_eq, LinearEquiv.mul_apply] using he.symm

theorem quotient_preserves_lie_submodules
    {k L V H : Type*} [Field k] [LieRing L] [LieAlgebra k L]
    [AddCommGroup V] [Module k V] [LieRingModule L V] [LieModule k L V] [Group H]
    (ρ : H →* (V ≃ₗ[k] V))
    (hstable : ∀ W : LieSubmodule k L V, ∀ g x, x ∈ W → ρ g x ∈ W)
    (W : LieSubmodule k L V)
    (hW : ∀ g, W.toSubmodule.map (ρ g).toLinearMap = W.toSubmodule) :
    ∀ U : LieSubmodule k L (V ⧸ W), ∀ g : (invariantQuotient ρ W.toSubmodule hW).range,
      ∀ x, x ∈ U → g.val x ∈ U := by
  intro U g x hx
  obtain ⟨g, hg⟩ := g
  obtain ⟨a, rfl⟩ := hg
  obtain ⟨v, rfl⟩ := LieSubmodule.Quotient.surjective_mk' W x
  have hv : v ∈ U.comap (LieSubmodule.Quotient.mk' W) := hx
  exact hstable (U.comap (LieSubmodule.Quotient.mk' W)) a v hv

theorem linearEquiv_comm_of_finrank_one
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (hV : Module.finrank k V = 1) (e f : V ≃ₗ[k] V) : e * f = f * e := by
  let : Nontrivial V := Module.nontrivial_of_finrank_pos (R := k) (M := V) (by omega)
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one hV hv (e v)
  obtain ⟨b, hb⟩ := exists_smul_eq_of_finrank_eq_one hV hv (f v)
  apply LinearEquiv.ext
  intro x
  obtain ⟨c, rfl⟩ := exists_smul_eq_of_finrank_eq_one hV hv x
  change e (f (c • v)) = f (e (c • v))
  simp only [map_smul, ← ha, ← hb, smul_smul]
  congr 1
  ring

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.LieInvariantSubspaces.Construction
