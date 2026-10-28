import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Pair

/-! # Action Maps -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.ActionMaps

noncomputable section

/-!
# The actual kernel action and its unit and composition maps
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u v

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [HasPullbacks C]
  {A B : C} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]

attribute [local instance] Scheme.kernelGroup

/-- The source of a kernel-action arrow. -/
abbrev source : A ⊗ Scheme.kernelObject f ⟶ A := fst _ _

/-- Translation by the full scheme-theoretic kernel. -/
def action : A ⊗ Scheme.kernelObject f ⟶ A :=
  source f * (snd _ _ ≫ Scheme.kernelInclusion f)

omit [IsMonHom f] in
theorem action_pair {T : C} (x : T ⟶ A) (k : T ⟶ Scheme.kernelObject f) :
    lift x k ≫ action f = x * (k ≫ Scheme.kernelInclusion f) := by
  simp only [action, MonObj.comp_mul, source, lift_fst, lift_snd_assoc]

/-- The identity-action section. -/
def unitSection : A ⟶ A ⊗ Scheme.kernelObject f := lift (𝟙 A) 1

theorem unitSection_source : unitSection f ≫ source f = 𝟙 A := lift_fst _ _

theorem unitSection_action : unitSection f ≫ action f = 𝟙 A := by
  rw [unitSection, action_pair, MonObj.one_comp, mul_one]

/-- The first arrow in a composable pair of kernel actions. -/
abbrev firstStep : (A ⊗ Scheme.kernelObject f) ⊗ Scheme.kernelObject f ⟶ A ⊗ Scheme.kernelObject f := fst _ _

/-- The second arrow starts at the endpoint of the first action. -/
def secondStep : (A ⊗ Scheme.kernelObject f) ⊗ Scheme.kernelObject f ⟶ A ⊗ Scheme.kernelObject f :=
  lift (firstStep f ≫ action f) (snd _ _)

/-- The composite action multiplies the two kernel elements. -/
def productStep : (A ⊗ Scheme.kernelObject f) ⊗ Scheme.kernelObject f ⟶ A ⊗ Scheme.kernelObject f :=
  lift (firstStep f ≫ source f) ((firstStep f ≫ snd _ _) * snd _ _)

abbrev tripleSource := firstStep f ≫ source f
abbrev tripleMiddle := firstStep f ≫ action f
abbrev tripleTarget := secondStep f ≫ action f

omit [IsMonHom f] in
theorem secondStep_source : secondStep f ≫ source f = tripleMiddle f := lift_fst _ _

theorem productStep_source : productStep f ≫ source f = tripleSource f := lift_fst _ _

/-- The endpoint of a composite kernel action is the endpoint after the two actions. -/
theorem productStep_action : productStep f ≫ action f = tripleTarget f := by
  change productStep f ≫ action f = secondStep f ≫ action f
  rw [productStep, action_pair, MonObj.mul_comp, secondStep, action_pair]
  rw [action, MonObj.comp_mul, ← Category.assoc, mul_assoc]

omit [GrpObj A] [IsMonHom f] in
/-- Pairing a point and a kernel element commutes with every change of test object. -/
theorem pair_naturality {T T' : C} (g : T' ⟶ T) (x : T ⟶ A) (k : T ⟶ Scheme.kernelObject f) :
    g ≫ lift x k = lift (g ≫ x) (g ≫ k) := by
  apply hom_ext <;> simp only [Category.assoc, lift_fst, lift_snd]

theorem unitSection_point {T : C} (x : T ⟶ A) :
    x ≫ unitSection f = lift x (1 : T ⟶ Scheme.kernelObject f) := by
  rw [unitSection, pair_naturality, Category.comp_id, MonObj.comp_one]

omit [GrpObj A] [IsMonHom f] in
theorem triple_firstStep {T : C} (x : T ⟶ A) (k l : T ⟶ Scheme.kernelObject f) :
    lift (lift x k) l ≫ firstStep f = lift x k := lift_fst _ _

omit [IsMonHom f] in
theorem triple_secondStep {T : C} (x : T ⟶ A) (k l : T ⟶ Scheme.kernelObject f) :
    lift (lift x k) l ≫ secondStep f = lift (x * (k ≫ Scheme.kernelInclusion f)) l := by
  rw [secondStep, pair_naturality, ← Category.assoc, triple_firstStep, action_pair, lift_snd]

theorem triple_productStep {T : C} (x : T ⟶ A) (k l : T ⟶ Scheme.kernelObject f) :
    lift (lift x k) l ≫ productStep f = lift x (k * l) := by
  rw [productStep, pair_naturality, ← Category.assoc, triple_firstStep, source, lift_fst,
    MonObj.comp_mul, ← Category.assoc, triple_firstStep, lift_snd, lift_snd]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.ActionMaps
