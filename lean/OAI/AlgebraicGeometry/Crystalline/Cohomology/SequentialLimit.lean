import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-! # Sequential Limit -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.SequentialLimit.SequentialLimitLifting

noncomputable section

/-!
# Lifting compatible sections through a sequential short exact system

Surjective transitions in the kernel let us correct arbitrary lifts at
each successive level. The resulting compatible lifts prove surjectivity
of the actual categorical inverse-limit map.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v

variable (R : Type u) [Ring R]

local instance : HasLimitsOfShape ℕᵒᵖ (ModuleCat.{v} R) := ModuleCat.hasLimitsOfShape

def transition (F : ℕᵒᵖ ⥤ (ModuleCat.{v} R)) (n : ℕ) : F.obj (op (n + 1)) →ₗ[R] F.obj (op n) :=
  (F.map (homOfLE (Nat.le_succ n)).op).hom

theorem naturality {F G : ℕᵒᵖ ⥤ (ModuleCat.{v} R)} (f : F ⟶ G) (n : ℕ) (z : F.obj (op (n + 1))) :
    f.app (op n) (transition R F n z) = transition R G n (f.app (op (n + 1)) z) :=
  ConcreteCategory.congr_hom (f.naturality (homOfLE (Nat.le_succ n)).op) z

variable (S : ShortComplex (ℕᵒᵖ ⥤ (ModuleCat.{v} R))) (hS : S.ShortExact)
  (hA : ∀ n, Function.Surjective (transition R S.X₁ n))
  (x : ∀ n, S.X₃.obj (op n)) (hx : ∀ n, transition R S.X₃ n (x (n + 1)) = x n)

include hS hA hx in
theorem step (n : ℕ) (y : S.X₂.obj (op n)) (hy : S.g.app (op n) y = x n) :
    ∃ z : S.X₂.obj (op (n + 1)), S.g.app (op (n + 1)) z = x (n + 1) ∧
      transition R S.X₂ n z = y := by
  have : Epi S.g := hS.epi_g
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (S.g.app (op (n + 1)))).mp inferInstance (x (n + 1))
  have hd : S.g.app (op n) (transition R S.X₂ n z - y) = 0 := by
    rw [map_sub, SequentialLimitLifting.naturality, hz, hx, hy, sub_self]
  have he := hS.exact.map ((evaluation ℕᵒᵖ (ModuleCat.{v} R)).obj (op n))
  obtain ⟨c, hc⟩ := (ShortComplex.moduleCat_exact_iff _).mp he _ hd
  obtain ⟨c', hc'⟩ := hA n c
  refine ⟨z - S.f.app (op (n + 1)) c', ?_, ?_⟩
  · rw [map_sub, hz]
    have hzero := ConcreteCategory.congr_hom (congr_app S.zero (op (n + 1))) c'
    change S.g.app (op (n + 1)) (S.f.app (op (n + 1)) c') = 0 at hzero
    rw [hzero, sub_zero]
  · rw [map_sub, ← SequentialLimitLifting.naturality, hc']
    change S.f.app (op n) c = transition R S.X₂ n z - y at hc
    rw [hc, sub_sub_cancel]

def lifts : ∀ n, {y : S.X₂.obj (op n) // S.g.app (op n) y = x n}
  | 0 => by
    have : Epi S.g := hS.epi_g
    exact ⟨Classical.choose ((ModuleCat.epi_iff_surjective (S.g.app (op 0))).mp inferInstance (x 0)),
      Classical.choose_spec ((ModuleCat.epi_iff_surjective (S.g.app (op 0))).mp inferInstance (x 0))⟩
  | n + 1 =>
    ⟨Classical.choose (SequentialLimitLifting.step R S hS hA x hx n (lifts n).val (lifts n).property),
      (Classical.choose_spec (SequentialLimitLifting.step R S hS hA x hx n (lifts n).val (lifts n).property)).1⟩

theorem lifts_compatible (n : ℕ) :
    transition R S.X₂ n (SequentialLimitLifting.lifts R S hS hA x hx (n + 1)).val = (SequentialLimitLifting.lifts R S hS hA x hx n).val :=
  (Classical.choose_spec (SequentialLimitLifting.step R S hS hA x hx n
    (SequentialLimitLifting.lifts R S hS hA x hx n).val (SequentialLimitLifting.lifts R S hS hA x hx n).property)).2

theorem compatible_all (F : ℕᵒᵖ ⥤ (ModuleCat.{v} R)) (y : ∀ n, F.obj (op n))
    (hy : ∀ n, transition R F n (y (n + 1)) = y n) {n m : ℕ} (h : n ≤ m) :
    F.map (homOfLE h).op (y m) = y n := by
  induction m, h using Nat.le_induction with
  | base =>
    have he : (homOfLE (Nat.le_refl n)).op = 𝟙 (op n) := Subsingleton.elim _ _
    rw [he, F.map_id]
    rfl
  | succ m h ih =>
    have he : (homOfLE (Nat.le.step h)).op =
        (homOfLE (Nat.le_succ m)).op ≫ (homOfLE h).op := Subsingleton.elim _ _
    rw [he, F.map_comp]
    change F.map (homOfLE h).op (transition R F m (y (m + 1))) = y n
    rw [hy, ih]

include hS hA in
theorem limit_surjective : Function.Surjective (limMap S.g) := by
  intro z
  let x : ∀ n, S.X₃.obj (op n) := fun n => limit.π S.X₃ (op n) z
  have hx : ∀ n, transition R S.X₃ n (x (n + 1)) = x n := fun n =>
    ConcreteCategory.congr_hom (limit.w S.X₃ (homOfLE (Nat.le_succ n)).op) z
  let y : ∀ n, S.X₂.obj (op n) := fun n => (SequentialLimitLifting.lifts R S hS hA x hx n).val
  let s : (S.X₂ ⋙ forget (ModuleCat.{v} R)).sections := ⟨fun n => y n.unop, fun {i j} f =>
    compatible_all R S.X₂ y (lifts_compatible R S hS hA x hx) (leOfHom f.unop)⟩
  let e := Types.isLimitEquivSections (isLimitOfPreserves (forget (ModuleCat.{v} R)) (limit.isLimit S.X₂))
  refine ⟨e.symm s, ?_⟩
  apply Concrete.limit_ext S.X₃
  intro n
  have he := Types.isLimitEquivSections_symm_apply
    (isLimitOfPreserves (forget (ModuleCat.{v} R)) (limit.isLimit S.X₂)) s n
  have hm := ConcreteCategory.congr_hom (limMap_π S.g n) (e.symm s)
  change limit.π S.X₃ n (limMap S.g (e.symm s)) = S.g.app n (limit.π S.X₂ n (e.symm s)) at hm
  exact hm.trans ((congrArg (S.g.app n) he).trans (SequentialLimitLifting.lifts R S hS hA x hx n.unop).property)

include hS hA in
theorem limit_epi : Epi (limMap S.g) :=
  (ModuleCat.epi_iff_surjective _).mpr (limit_surjective R S hS hA)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.SequentialLimit.SequentialLimitLifting
