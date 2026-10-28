import OAI.AlgebraicGeometry.Quotients.FiniteDescent.GroupOperationsIs
import Mathlib.CategoryTheory.Limits.Shapes.KernelPair

/-! # Group -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.Group.Construction.GroupDescent

/-!
# Descending the group operations through a translation quotient

An exact translation kernel pair implies invariance and compatibility with
multiplication and inversion. Effective epimorphisms then construct the
target operations, and the group laws follow from `GroupOperations`.
-/

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u v

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    {A B H : C} [GrpObj A] (i : H ⟶ A) (q : A ⟶ B)

abbrev translation : H ⊗ A ⟶ A := (fst H A ≫ i) * snd H A

variable (hk : IsKernelPair q (snd H A) (translation i))

include hk in
/-- A quotient with the translation kernel pair is invariant under every
subgroup-valued point. -/
theorem invariant {T : C} (a : T ⟶ A) (h : T ⟶ H) :
    ((h ≫ i) * a) ≫ q = a ≫ q := by
  have he := congrArg (fun f => lift h a ≫ f) hk.w
  simp only [← Category.assoc] at he
  simpa only [lift_snd, translation, MonObj.comp_mul, lift_fst_assoc] using he.symm

include hk in
/-- Equal quotient-valued points differ by a subgroup translation. -/
theorem exists_translate {T : C} (a b : T ⟶ A) (hab : a ≫ q = b ≫ q) :
    ∃ h : T ⟶ H, (h ≫ i) * b = a := by
  let r := hk.lift b a hab.symm
  have hs : r ≫ snd H A = b := hk.lift_fst _ _ _
  have ht : r ≫ translation i = a := hk.lift_snd _ _ _
  refine ⟨r ≫ fst H A, ?_⟩
  simpa only [translation, MonObj.comp_mul, ← Category.assoc, hs] using ht

include hk in
/-- The fiber over the image of the identity is exactly the subgroup, on
every test object, including uniqueness of the subgroup-valued lift. -/
theorem kernel [Mono i] (T : C) (a : T ⟶ A) :
    a ≫ q = (1 : T ⟶ A) ≫ q ↔ ∃! h : T ⟶ H, h ≫ i = a := by
  constructor
  · intro ha
    obtain ⟨h, hh⟩ := exists_translate i q hk a 1 ha
    rw [mul_one] at hh
    exact ⟨h, hh, fun h' hh' => (cancel_mono i).mp (hh'.trans hh.symm)⟩
  · rintro ⟨h, rfl, _⟩
    simpa only [mul_one] using invariant i q hk (1 : T ⟶ A) h

variable [GrpObj H] [IsMonHom i] [BraidedCategory C] [IsCommMonObj A]

include hk in
theorem mul_congr {T : C} (a a' b b' : T ⟶ A)
    (ha : a ≫ q = a' ≫ q) (hb : b ≫ q = b' ≫ q) :
    (a * b) ≫ q = (a' * b') ≫ q := by
  obtain ⟨h, hh⟩ := exists_translate i q hk a a' ha
  obtain ⟨k, hk'⟩ := exists_translate i q hk b b' hb
  rw [← hh, ← hk', mul_mul_mul_comm, ← MonObj.mul_comp]
  exact invariant i q hk (a' * b') (h * k)

include hk in
theorem inv_congr {T : C} (a b : T ⟶ A) (hab : a ≫ q = b ≫ q) :
    a⁻¹ ≫ q = b⁻¹ ≫ q := by
  obtain ⟨h, hh⟩ := exists_translate i q hk a b hab
  rw [← hh, mul_inv, ← GrpObj.inv_comp]
  exact invariant i q hk b⁻¹ h⁻¹

include hk in
theorem multiplication_compatible :
    ∀ {T : C} (a b : T ⟶ A ⊗ A), a ≫ (q ⊗ₘ q) = b ≫ (q ⊗ₘ q) →
      a ≫ MonObj.mul ≫ q = b ≫ MonObj.mul ≫ q := by
  intro T a b hab
  have h₁ : (a ≫ fst A A) ≫ q = (b ≫ fst A A) ≫ q := by
    simpa using congrArg (fun f => f ≫ fst B B) hab
  have h₂ : (a ≫ snd A A) ≫ q = (b ≫ snd A A) ≫ q := by
    simpa using congrArg (fun f => f ≫ snd B B) hab
  simpa [Hom.mul_def] using mul_congr i q hk
    (a ≫ fst A A) (b ≫ fst A A) (a ≫ snd A A) (b ≫ snd A A) h₁ h₂

include hk in
theorem inverse_compatible :
    ∀ {T : C} (a b : T ⟶ A), a ≫ q = b ≫ q →
      a ≫ GrpObj.inv ≫ q = b ≫ GrpObj.inv ≫ q := by
  intro T a b hab
  simpa only [Hom.inv_def, Category.assoc] using inv_congr i q hk a b hab

variable [EffectiveEpi q] [EffectiveEpi (q ⊗ₘ q)]

/-- Multiplication on the quotient, constructed by effective descent. -/
noncomputable def multiplication : B ⊗ B ⟶ B :=
  EffectiveEpi.desc (q ⊗ₘ q) (MonObj.mul ≫ q) (multiplication_compatible i q hk)

omit [EffectiveEpi q] in
theorem multiplication_fac : (q ⊗ₘ q) ≫ multiplication i q hk = MonObj.mul ≫ q :=
  EffectiveEpi.fac (q ⊗ₘ q) (MonObj.mul ≫ q) (multiplication_compatible i q hk)

/-- Inversion on the quotient, constructed by effective descent. -/
noncomputable def inverse : B ⟶ B :=
  EffectiveEpi.desc q (GrpObj.inv ≫ q) (inverse_compatible i q hk)

omit [EffectiveEpi (q ⊗ₘ q)] in
theorem inverse_fac : q ≫ inverse i q hk = GrpObj.inv ≫ q :=
  EffectiveEpi.fac q (GrpObj.inv ≫ q) (inverse_compatible i q hk)

variable [Epi ((q ⊗ₘ q) ⊗ₘ q)]

/-- The commutative group structure on a translation quotient. -/
@[instance_reducible]
noncomputable def group : GrpObj B :=
  GroupOperationsIs.Construction.GroupOperations.group q (multiplication i q hk) (multiplication_fac i q hk)
    (inverse i q hk) (inverse_fac i q hk)

theorem isMonHom_group : letI := group i q hk; IsMonHom q :=
  GroupOperationsIs.Construction.GroupOperations.isMonHom_group q (multiplication i q hk) (multiplication_fac i q hk)
    (inverse i q hk) (inverse_fac i q hk)

theorem isCommMonObj_group : letI := group i q hk; IsCommMonObj B :=
  GroupOperationsIs.Construction.GroupOperations.isCommMonObj_group q (multiplication i q hk) (multiplication_fac i q hk)
    (inverse i q hk) (inverse_fac i q hk)

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.Group.Construction.GroupDescent
