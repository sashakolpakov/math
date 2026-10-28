/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Nailin Guan
This file has been modified.
-/
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Data.ENat.Lattice

/-! # Dimension Basic -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.DimensionBasic

/-!
# Projective dimension

In an abelian category `C`, we shall say that `X: C` has projective dimension `< n`
if all `Ext X Y i` vanish when `n ≤ i`. This defines a type class
`HasProjectiveDimensionLT X n`. We also define a type class
`HasProjectiveDimensionLE X n` as an abbreviation for
`HasProjectiveDimensionLT X (n + 1)`.
(Note that the fact that `X` is a zero object is equivalent to the condition
`HasProjectiveDimensionLT X 0`, but this cannot be expressed in terms of
`HasProjectiveDimensionLE`.)

We also define the projective dimension in `WithBot ℕ∞` as `projectiveDimension`,
`projectiveDimension X = ⊥` iff `X` is zero and behaves as expected on non-negative values.

-/

universe w v u

section

open _root_.CategoryTheory _root_.CategoryTheory.Abelian _root_.CategoryTheory.Limits

open ZeroObject

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- An object `X` in an abelian category has projective dimension `< n` if
all `Ext X Y i` vanish when `n ≤ i`. See also `HasProjectiveDimensionLE`.
(Do not use the `subsingleton'` field directly. Use the constructor
`HasProjectiveDimensionLT.mk`, and the lemmas `hasProjectiveDimensionLT_iff` and
`Ext.eq_zero_of_hasProjectiveDimensionLT`.) -/
class HasProjectiveDimensionLT (X : C) (n : ℕ) : Prop where mk' ::
  subsingleton' (i : ℕ) (hi : n ≤ i) ⦃Y : C⦄ :
    let := HasExt.standard C
    Subsingleton (Ext.{max u v} X Y i)

/-- An object `X` in an abelian category has projective dimension `≤ n` if
all `Ext X Y i` vanish when `n + 1 ≤ i` -/
abbrev HasProjectiveDimensionLE (X : C) (n : ℕ) : Prop :=
  HasProjectiveDimensionLT X (n + 1)

namespace HasProjectiveDimensionLT

variable [HasExt.{w} C] (X : C) (n : ℕ)

lemma subsingleton [hX : HasProjectiveDimensionLT X n] (i : ℕ) (hi : n ≤ i) (Y : C) :
    Subsingleton (Ext.{w} X Y i) := by
  let := HasExt.standard C
  have := hX.subsingleton' i hi
  exact Ext.chgUniv.{w, max u v}.symm.subsingleton

variable {X n} in
lemma mk (hX : ∀ (i : ℕ) (_ : n ≤ i) ⦃Y : C⦄, ∀ (e : Ext X Y i), e = 0) :
    HasProjectiveDimensionLT X n where
  subsingleton' i hi Y := by
    have : Subsingleton (Ext X Y i) := ⟨fun e₁ e₂ ↦ by simp only [hX i hi]⟩
    let := HasExt.standard C
    exact Ext.chgUniv.{max u v, w}.symm.subsingleton

end HasProjectiveDimensionLT

lemma Abelian.Ext.eq_zero_of_hasProjectiveDimensionLT [HasExt.{w} C]
    {X Y : C} {i : ℕ} (e : Ext X Y i) (n : ℕ) [HasProjectiveDimensionLT X n]
    (hi : n ≤ i) : e = 0 :=
  (HasProjectiveDimensionLT.subsingleton X n i hi Y).elim _ _

section

variable (X : C) (n : ℕ)

lemma hasProjectiveDimensionLT_iff [HasExt.{w} C] :
    HasProjectiveDimensionLT X n ↔
      ∀ (i : ℕ) (_ : n ≤ i) ⦃Y : C⦄, ∀ (e : Ext X Y i), e = 0 :=
  ⟨fun _ _ hi _ e ↦ DimensionBasic.Abelian.Ext.eq_zero_of_hasProjectiveDimensionLT e n hi,
    HasProjectiveDimensionLT.mk⟩

variable {X} in
lemma Limits.IsZero.hasProjectiveDimensionLT_zero (hX : IsZero X) :
    HasProjectiveDimensionLT X 0 := by
  let := HasExt.standard C
  rw [hasProjectiveDimensionLT_iff]
  intro i hi Y e
  rw [← e.mk₀_id_comp, hX.eq_of_src (𝟙 X) 0, Ext.mk₀_zero, Ext.zero_comp]

instance : HasProjectiveDimensionLT (0 : C) 0 :=
  DimensionBasic.Limits.IsZero.hasProjectiveDimensionLT_zero (isZero_zero C)

lemma isZero_of_hasProjectiveDimensionLT_zero [HasProjectiveDimensionLT X 0] : IsZero X := by
  let := HasExt.standard C
  rw [IsZero.iff_id_eq_zero]
  apply Ext.homEquiv₀.symm.injective
  simpa only [Ext.homEquiv₀_symm_apply, Ext.mk₀_zero]
    using DimensionBasic.Abelian.Ext.eq_zero_of_hasProjectiveDimensionLT _ 0 (by rfl)

lemma hasProjectiveDimensionLT_zero_iff_isZero : HasProjectiveDimensionLT X 0 ↔ IsZero X :=
  ⟨fun _ ↦ isZero_of_hasProjectiveDimensionLT_zero X,
    fun h ↦ DimensionBasic.Limits.IsZero.hasProjectiveDimensionLT_zero h⟩

lemma hasProjectiveDimensionLT_of_ge (m : ℕ) (h : n ≤ m)
    [HasProjectiveDimensionLT X n] :
    HasProjectiveDimensionLT X m := by
  let := HasExt.standard C
  rw [hasProjectiveDimensionLT_iff]
  intro i hi Y e
  exact DimensionBasic.Abelian.Ext.eq_zero_of_hasProjectiveDimensionLT e n (by lia)

instance [HasProjectiveDimensionLT X n] (k : ℕ) :
    HasProjectiveDimensionLT X (n + k) :=
  hasProjectiveDimensionLT_of_ge X n (n + k) (by lia)

instance [HasProjectiveDimensionLT X n] (k : ℕ) :
    HasProjectiveDimensionLT X (k + n) :=
  hasProjectiveDimensionLT_of_ge X n (k + n) (by lia)

instance [HasProjectiveDimensionLT X n] :
    HasProjectiveDimensionLT X n.succ :=
  inferInstanceAs (HasProjectiveDimensionLT X (n + 1))

instance [Projective X] : HasProjectiveDimensionLT X 1 := by
  let := HasExt.standard C
  rw [hasProjectiveDimensionLT_iff]
  intro i hi Y e
  obtain _ | i := i
  · simp at hi
  · exact e.eq_zero_of_projective

variable {X} in
lemma projective_iff_subsingleton_ext_one [HasExt.{w} C] :
    Projective X ↔ ∀ ⦃Y : C⦄, Subsingleton (Ext X Y 1) := by
  refine ⟨fun h ↦ HasProjectiveDimensionLT.subsingleton X 1 1 (by rfl),
    fun h ↦ ⟨fun f g _ ↦ ?_⟩⟩
  have : Epi (ShortComplex.kernelSequence g).g := by
    change Epi g
    infer_instance
  obtain ⟨φ, hφ⟩ :=
    Ext.covariant_sequence_exact₃ _ { exact := ShortComplex.kernelSequence_exact g }
      (Ext.mk₀ f) (zero_add 1) (by subsingleton)
  obtain ⟨φ, rfl⟩ := Ext.homEquiv₀.symm.surjective φ
  exact ⟨φ, Ext.homEquiv₀.symm.injective ((Ext.mk₀_comp_mk₀ φ g).symm.trans hφ)⟩

variable {X} in
lemma projective_iff_hasProjectiveDimensionLT_one :
    Projective X ↔ HasProjectiveDimensionLT X 1 := by
  let := HasExt.standard C
  exact ⟨fun _ ↦ inferInstance, fun _ ↦ projective_iff_subsingleton_ext_one.2
    (HasProjectiveDimensionLT.subsingleton X 1 1 (by rfl))⟩

lemma projective_iff_hasProjectiveDimensionLE_zero : Projective X ↔ HasProjectiveDimensionLE X 0 :=
  projective_iff_hasProjectiveDimensionLT_one

instance (priority := low) [HasProjectiveDimensionLT X 1] : Projective X :=
  projective_iff_hasProjectiveDimensionLT_one.mpr ‹_›

end

lemma Retract.hasProjectiveDimensionLT {X Y : C} (h : Retract X Y) (n : ℕ)
    [HasProjectiveDimensionLT Y n] :
    HasProjectiveDimensionLT X n := by
  let := HasExt.standard C
  rw [hasProjectiveDimensionLT_iff]
  intro i hi T x
  rw [← x.mk₀_id_comp, ← h.retract, ← Ext.mk₀_comp_mk₀,
    Ext.comp_assoc_of_second_deg_zero,
    DimensionBasic.Abelian.Ext.eq_zero_of_hasProjectiveDimensionLT
      ((Ext.mk₀ h.r).comp x (zero_add i)) n hi,
    Ext.comp_zero]

lemma hasProjectiveDimensionLT_of_iso {X X' : C} (e : X ≅ X') (n : ℕ)
    [HasProjectiveDimensionLT X n] :
    HasProjectiveDimensionLT X' n :=
  DimensionBasic.Retract.hasProjectiveDimensionLT e.symm.retract n

namespace ShortComplex.ShortExact
open _root_.CategoryTheory.ShortComplex

open _root_.CategoryTheory.ShortComplex.ShortExact

variable {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ)
include hS

-- In the following lemmas, the parameters `HasProjectiveDimensionLT` are
-- explicit as it is unlikely we may infer them, unless the short complex `S`
-- was declared reducible

lemma hasProjectiveDimensionLT_X₂ (h₁ : HasProjectiveDimensionLT S.X₁ n)
    (h₃ : HasProjectiveDimensionLT S.X₃ n) :
    HasProjectiveDimensionLT S.X₂ n := by
  let := HasExt.standard C
  rw [hasProjectiveDimensionLT_iff]
  intro i hi Y x₂
  obtain ⟨x₃, rfl⟩ := Ext.contravariant_sequence_exact₂ hS _ x₂
    (DimensionBasic.Abelian.Ext.eq_zero_of_hasProjectiveDimensionLT _ n hi)
  rw [DimensionBasic.Abelian.Ext.eq_zero_of_hasProjectiveDimensionLT x₃ n hi, Ext.comp_zero]

lemma hasProjectiveDimensionLT_X₃ (h₁ : HasProjectiveDimensionLT S.X₁ n)
    (h₂ : HasProjectiveDimensionLT S.X₂ (n + 1)) :
    HasProjectiveDimensionLT S.X₃ (n + 1) := by
  let := HasExt.standard C
  rw [hasProjectiveDimensionLT_iff]
  rintro (_ | i) hi Y x₃
  · simp at hi
  · obtain ⟨x₁, rfl⟩ := Ext.contravariant_sequence_exact₃ hS _ x₃
      (DimensionBasic.Abelian.Ext.eq_zero_of_hasProjectiveDimensionLT _ (n + 1) hi) (add_comm _ _)
    rw [DimensionBasic.Abelian.Ext.eq_zero_of_hasProjectiveDimensionLT x₁ n (by lia), Ext.comp_zero]

lemma hasProjectiveDimensionLT_X₁ (h₂ : HasProjectiveDimensionLT S.X₂ n)
    (h₃ : HasProjectiveDimensionLT S.X₃ (n + 1)) :
    HasProjectiveDimensionLT S.X₁ n := by
  let := HasExt.standard C
  rw [hasProjectiveDimensionLT_iff]
  intro i hi Y x₁
  obtain ⟨x₂, rfl⟩ := Ext.contravariant_sequence_exact₁ hS _ x₁ (add_comm _ _)
    (DimensionBasic.Abelian.Ext.eq_zero_of_hasProjectiveDimensionLT _ (n + 1) (by lia))
  rw [DimensionBasic.Abelian.Ext.eq_zero_of_hasProjectiveDimensionLT x₂ n (by lia), Ext.comp_zero]

lemma hasProjectiveDimensionLT_X₃_iff (n : ℕ) (h₂ : Projective S.X₂) :
    HasProjectiveDimensionLT S.X₃ (n + 2) ↔ HasProjectiveDimensionLT S.X₁ (n + 1) :=
  ⟨fun _ ↦ hasProjectiveDimensionLT_X₁
      hS (n + 1) inferInstance inferInstance,
    fun _ ↦ hasProjectiveDimensionLT_X₃
      hS (n + 1) inferInstance inferInstance⟩

end ShortComplex.ShortExact

instance (X Y : C) (n : ℕ) [HasProjectiveDimensionLT X n] [HasProjectiveDimensionLT Y n] :
    HasProjectiveDimensionLT (X ⊞ Y) n :=
  DimensionBasic.ShortComplex.ShortExact.hasProjectiveDimensionLT_X₂
    (ShortComplex.Splitting.ofHasBinaryBiproduct X Y).shortExact n ‹_› ‹_›

lemma hasProjectiveDimensionLT_of_enoughInjectives [HasExt.{w} C] [EnoughInjectives C] (X : C)
    (n : ℕ) (hX : ∀ Y : C, Subsingleton (Ext X Y n)) : HasProjectiveDimensionLT X n := by
  suffices ∀ ⦃d : ℕ⦄ ⦃Y : C⦄ (e : Ext X Y d) (k : ℕ), d = n + k → e = 0 from
    HasProjectiveDimensionLT.mk (fun i hi Y e ↦ by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hi
      exact this e k rfl)
  intro d Y e k hd
  induction k generalizing d Y with
  | zero =>
    obtain rfl : d = n := by simpa using hd
    subsingleton
  | succ k hk =>
    let ⟨p⟩ := EnoughInjectives.presentation Y
    have h : (ShortComplex.mk _ _ (cokernel.condition p.f)).ShortExact :=
      { exact := ShortComplex.cokernelSequence_exact p.f }
    have hd : n + k + 1 = d := by lia
    obtain ⟨x, rfl⟩ := Ext.covariant_sequence_exact₁ X h e
      (by subst hd; apply Ext.eq_zero_of_injective) hd
    simp [hk x rfl]

end

open _root_.CategoryTheory _root_.CategoryTheory.Abelian _root_.CategoryTheory.Limits

variable {C : Type u} [Category.{v, u} C] [Abelian C]

/-- The projective dimension of an object in an abelian category. -/
noncomputable def projectiveDimension (X : C) : WithBot ℕ∞ :=
  sInf {n : WithBot ℕ∞ | ∀ (i : ℕ), n < i → HasProjectiveDimensionLT X i}

lemma projectiveDimension_eq_of_iso {X Y : C} (e : X ≅ Y) :
    projectiveDimension X = projectiveDimension Y := by
  simp only [projectiveDimension]
  congr! 5
  exact ⟨fun h ↦ hasProjectiveDimensionLT_of_iso e _,
    fun h ↦ hasProjectiveDimensionLT_of_iso e.symm _⟩

lemma Retract.projectiveDimension_le {X Y : C} (h : Retract X Y) :
    projectiveDimension X ≤ projectiveDimension Y :=
  sInf_le_sInf_of_subset_insert_top (fun n hn ↦ by
    simp only [Set.mem_ofPred_eq, not_top_lt, IsEmpty.forall_iff, implies_true,
      Set.insert_eq_of_mem] at hn ⊢
    intro i hi
    have := hn i hi
    exact DimensionBasic.Retract.hasProjectiveDimensionLT h i)

lemma projectiveDimension_lt_iff {X : C} {n : ℕ} :
    projectiveDimension X < n ↔ HasProjectiveDimensionLT X n := by
  refine ⟨fun h ↦ ?_, fun h ↦ sInf_lt_iff.2 ?_⟩
  · have : projectiveDimension X ∈ _ := csInf_mem ⟨⊤, by simp⟩
    simp only [Set.mem_ofPred_eq] at this
    exact this _ h
  · obtain _ | n := n
    · exact ⟨⊥, fun _ _ ↦ hasProjectiveDimensionLT_of_ge _ 0 _ (by simp), by decide⟩
    · exact ⟨n, fun i hi ↦ hasProjectiveDimensionLT_of_ge _ (n + 1) _ (by simpa using hi),
        by simp [ENat.WithBot.lt_add_one_iff]⟩

lemma projectiveDimension_le_iff (X : C) (n : ℕ) :
    projectiveDimension X ≤ n ↔ HasProjectiveDimensionLE X n := by
  simp [← projectiveDimension_lt_iff, ← ENat.WithBot.lt_add_one_iff]

lemma projectiveDimension_ge_iff (X : C) (n : ℕ) :
    n ≤ projectiveDimension X ↔ ¬ HasProjectiveDimensionLT X n := by
  contrapose!; exact projectiveDimension_lt_iff

lemma projectiveDimension_eq_bot_iff (X : C) :
    projectiveDimension X = ⊥ ↔ Limits.IsZero X := by
  rw [← hasProjectiveDimensionLT_zero_iff_isZero, ← projectiveDimension_lt_iff,
    Nat.cast_zero, ← WithBot.lt_coe_bot, bot_eq_zero', WithBot.coe_zero]

lemma projectiveDimension_ne_top_iff (X : C) :
    projectiveDimension X ≠ ⊤ ↔ ∃ n, HasProjectiveDimensionLE X n := by
  generalize hd : projectiveDimension X = d
  induction d with
  | bot =>
    simp only [ne_eq, bot_ne_top, not_false_eq_true, true_iff]
    exact ⟨0, by simp [← projectiveDimension_le_iff, hd]⟩
  | coe d =>
    induction d with
    | top =>
      by_contra!
      simp only [WithBot.coe_top, ne_eq, not_true_eq_false, false_and, true_and, false_or] at this
      obtain ⟨n, hn⟩ := this
      rw [← projectiveDimension_le_iff, hd, WithBot.coe_top, top_le_iff] at hn
      exact ENat.natCast_ne_top _ ((WithBot.coe_eq_coe).1 hn)
    | coe d =>
      simp only [ne_eq, WithBot.coe_eq_top, ENat.natCast_ne_top, not_false_eq_true, true_iff]
      exact ⟨d, by simpa only [← projectiveDimension_le_iff] using! hd.le⟩

lemma projectiveDimension_eq_zero_iff (X : C) :
    projectiveDimension X = 0 ↔ Projective X ∧ ¬ Limits.IsZero X := by
  rw [← projectiveDimension_eq_bot_iff, projective_iff_hasProjectiveDimensionLE_zero,
    ← projectiveDimension_le_iff, ← WithBot.lt_zero_iff_eq_bot, not_lt, Nat.cast_zero,
    le_antisymm_iff]

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.DimensionBasic
