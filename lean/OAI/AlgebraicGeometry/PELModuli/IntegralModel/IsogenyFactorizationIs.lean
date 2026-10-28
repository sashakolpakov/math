import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.Algebra.Group.Subgroup.Basic
import Lean.Util.CollectAxioms

/-! # Isogeny Factorization Is -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.IsogenyFactorizationIs.IsogenyFactorization

/-! The elementary quotient-factorization part of the proved PoincareBundle argument,
reproduced from c513c6952388259cb3bee49fc59d39ce8dd1bb5f. This owned module
retains only the native effective-epimorphism and group-object proof, so the
IntegralModel isogeny construction is independent of concurrent edits to PoincareBundle's
unrelated line-bundle descent imports. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry

universe u v

section Categorical

variable {C : Type u} [Category.{v} C]

/-- Pullback along an epimorphism is injective when the target is a dual
object for a contravariant equivalence. -/
theorem dual_pullback_injective
    (D : Cᵒᵖ ≌ C) {A B : C} (f : A ⟶ B) [Epi f] :
    Function.Injective
      (fun p : B ⟶ D.functor.obj (op B) => f ≫ p ≫ D.functor.map f.op) := by
  intro p r h
  have : Mono (D.functor.map f.op) := inferInstance
  apply (cancel_mono (D.functor.map f.op)).mp
  apply (cancel_epi f).mp
  simpa only [Category.assoc] using h

/-- Relations in the slice detect the underlying relations. -/
theorem over_coequalizes_left {S : C} {A B W : Over S}
    (f : A ⟶ B) (g : A ⟶ W)
    (hg : ∀ {T : Over S} (x y : T ⟶ A),
      x ≫ f = y ≫ f → x ≫ g = y ≫ g) :
    ∀ {T : C} (x y : T ⟶ A.left),
      x ≫ f.left = y ≫ f.left → x ≫ g.left = y ≫ g.left := by
  intro T x y hxy
  let T' : Over S := Over.mk (x ≫ A.hom)
  let x' : T' ⟶ A := Over.homMk x rfl
  let y' : T' ⟶ A := Over.homMk y (by
    change y ≫ A.hom = x ≫ A.hom
    rw [← Over.w f, ← Category.assoc, ← Category.assoc, hxy])
  exact congrArg Over.Hom.left (hg x' y' (Over.OverMorphism.ext hxy))

/-- Effective epimorphisms of the underlying objects remain effective
epimorphisms in a slice category. -/
theorem effectiveEpi_over_of_left {S : C} {A B : Over S}
    (f : A ⟶ B) [EffectiveEpi f.left] : EffectiveEpi f := by
  constructor
  refine ⟨{
    desc := fun {W} g hg => ?_
    fac := ?_
    uniq := ?_
  }⟩
  · have hrel : ∀ {T : C} (x y : T ⟶ A.left),
        x ≫ f.left = y ≫ f.left → x ≫ g.left = y ≫ g.left :=
      over_coequalizes_left f g hg
    let d := EffectiveEpi.desc f.left g.left hrel
    refine Over.homMk d ?_
    apply (cancel_epi f.left).mp
    rw [← Category.assoc, EffectiveEpi.fac, Over.w g, Over.w f]
  · intro W g hg
    apply Over.OverMorphism.ext
    dsimp
    apply EffectiveEpi.fac
    exact over_coequalizes_left f g hg
  · intro W g hg m hm
    apply Over.OverMorphism.ext
    exact EffectiveEpi.uniq f.left g.left (over_coequalizes_left f g hg)
      m.left (congrArg Over.Hom.left hm)

end Categorical

section GroupObjects

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable {A B Z : C} [GrpObj A] [GrpObj B] [GrpObj Z]

/-- A homomorphism which kills the kernel of an effective quotient
descends uniquely as a morphism. The hypothesis tests the kernel on all
objects, so it also detects nonreduced subgroup schemes. -/
theorem exists_unique_morphism_of_kernel_trivial
    (f : A ⟶ B) [IsMonHom f] [EffectiveEpi f]
    (g : A ⟶ Z) [IsMonHom g]
    (hker : ∀ (T : C) (x : T ⟶ A), x ≫ f = 1 → x ≫ g = 1) :
    ∃! d : B ⟶ Z, f ≫ d = g := by
  have hrel : ∀ {T : C} (x y : T ⟶ A),
      x ≫ f = y ≫ f → x ≫ g = y ≫ g := by
    intro T x y hxy
    have hk : (x / y) ≫ f = 1 := by rw [GrpObj.div_comp, hxy, div_self']
    have hd := hker T (x / y) hk
    rw [GrpObj.div_comp, div_eq_one] at hd
    exact hd
  exact ⟨EffectiveEpi.desc f g hrel, EffectiveEpi.fac f g hrel,
    fun d hd => EffectiveEpi.uniq f g hrel d hd⟩

/-- The descended morphism preserves the group law when the product
of the quotient with itself is epimorphic. -/
theorem isMonHom_of_comp
    (f : A ⟶ B) [IsMonHom f] [Epi (f ⊗ₘ f)]
    (g : A ⟶ Z) [IsMonHom g] (d : B ⟶ Z)
    (hd : f ≫ d = g) : IsMonHom d := by
  constructor
  · rw [← IsMonHom.one_hom f, Category.assoc, hd, IsMonHom.one_hom g]
  · apply (cancel_epi (f ⊗ₘ f)).mp
    rw [← Category.assoc, ← IsMonHom.mul_hom f, Category.assoc, hd,
      IsMonHom.mul_hom g]
    rw [← Category.assoc, tensorHom_comp_tensorHom, hd]

/-- Descent of a group homomorphism from the kernel criterion. -/
theorem exists_unique_hom_of_kernel_trivial
    (f : A ⟶ B) [IsMonHom f] [EffectiveEpi f] [Epi (f ⊗ₘ f)]
    (g : A ⟶ Z) [IsMonHom g]
    (hker : ∀ (T : C) (x : T ⟶ A), x ≫ f = 1 → x ≫ g = 1) :
    ∃! d : B ⟶ Z, IsMonHom d ∧ f ≫ d = g := by
  obtain ⟨d, hd, hu⟩ := exists_unique_morphism_of_kernel_trivial f g hker
  exact ⟨d, ⟨isMonHom_of_comp f g d hd, hd⟩, fun e he => hu e he.2⟩

variable [BraidedCategory C]

/-- Pointwise integer multiplication of a homomorphism into a commutative
group object is again a homomorphism. Multiplicative notation is used
because mathlib's group-object API uses `GrpObj`. -/
theorem isMonHom_pow [IsCommMonObj Z]
    (g : A ⟶ Z) [IsMonHom g] (n : ℕ) : IsMonHom (g ^ n) := by
  induction n with
  | zero =>
      change IsMonHom (1 : A ⟶ Z)
      change IsMonHom (toUnit A ≫ η[Z])
      infer_instance
  | succ n ih =>
      have : IsMonHom (g ^ n) := ih
      rw [pow_succ, Hom.mul_def]
      infer_instance

/-- If the quotient kernel is killed by n, then n times any homomorphism
out of the source descends uniquely through the quotient. -/
theorem exists_unique_multiple_descent
    [IsCommMonObj Z]
    (f : A ⟶ B) [IsMonHom f] [EffectiveEpi f] [Epi (f ⊗ₘ f)]
    (g : A ⟶ Z) [IsMonHom g] (n : ℕ)
    (hker : ∀ (T : C) (x : T ⟶ A), x ≫ f = 1 → x ^ n = 1) :
    ∃! d : B ⟶ Z, IsMonHom d ∧ f ≫ d = g ^ n := by
  have : IsMonHom (g ^ n) := isMonHom_pow g n
  apply exists_unique_hom_of_kernel_trivial f (g ^ n)
  intro T x hx
  rw [MonObj.comp_pow, ← MonObj.pow_comp, hker T x hx, MonObj.one_comp]

end GroupObjects

/-- Flat surjections which are quasi-compact are effective quotients
also as morphisms over their base scheme. -/
theorem effectiveEpi_over_of_fpqc
    {S : Scheme.{u}} {A B : Over S} (f : A ⟶ B)
    [Flat f.left] [Surjective f.left] [QuasiCompact f.left] :
    EffectiveEpi f :=
  effectiveEpi_over_of_left f

/-- A property stable under composition and base change is preserved
by products of morphisms over a fixed base. -/
theorem property_tensor_over
    (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] [P.IsStableUnderComposition]
    {S : Scheme.{u}} {A B X Y : Over S}
    (f : A ⟶ B) (g : X ⟶ Y) (hf : P f.left) (hg : P g.left) :
    P (f ⊗ₘ g).left := by
  rw [Over.tensorHom_left]
  exact MorphismProperty.pullbackMap hf hg (Over.w f).symm (Over.w g).symm

/-- The product of two fpqc quotient morphisms is still an effective
epimorphism in the slice category. -/
theorem effectiveEpi_tensor_over_of_fpqc
    {S : Scheme.{u}} {A B X Y : Over S}
    (f : A ⟶ B) (g : X ⟶ Y)
    [Flat f.left] [Surjective f.left] [QuasiCompact f.left]
    [Flat g.left] [Surjective g.left] [QuasiCompact g.left] :
    EffectiveEpi (f ⊗ₘ g) := by
  let : MorphismProperty.IsStableUnderComposition
      (@AlgebraicGeometry.Surjective.{u}) :=
    ⟨fun _ _ hf hg => ⟨hg.1.comp hf.1⟩⟩
  have : Flat (f ⊗ₘ g).left := property_tensor_over (@Flat) f g inferInstance inferInstance
  have : Surjective (f ⊗ₘ g).left :=
    property_tensor_over (@AlgebraicGeometry.Surjective) f g inferInstance inferInstance
  have : QuasiCompact (f ⊗ₘ g).left :=
    property_tensor_over (@QuasiCompact) f g inferInstance inferInstance
  exact effectiveEpi_over_of_fpqc (f ⊗ₘ g)

/-- A group-scheme homomorphism which vanishes on the scheme-theoretic
kernel of an fpqc quotient has a unique descended group-scheme homomorphism.
Testing all S-schemes retains infinitesimal, nonreduced kernel data. -/
theorem fpqc_group_hom_descent
    {S : Scheme.{u}} {A B Z : Over S}
    [GrpObj A] [GrpObj B] [GrpObj Z]
    (f : A ⟶ B) [IsMonHom f]
    [Flat f.left] [Surjective f.left] [QuasiCompact f.left]
    (g : A ⟶ Z) [IsMonHom g]
    (hker : ∀ (T : Over S) (x : T ⟶ A), x ≫ f = 1 → x ≫ g = 1) :
    ∃! d : B ⟶ Z, IsMonHom d ∧ f ≫ d = g := by
  have : EffectiveEpi f := effectiveEpi_over_of_fpqc f
  have : EffectiveEpi (f ⊗ₘ f) := effectiveEpi_tensor_over_of_fpqc f f
  exact exists_unique_hom_of_kernel_trivial f g hker

/-- First factorization in PoincareBundle: containment of the isogeny kernel in
A[n] makes n times a homomorphism factor through the quotient.
This is a scheme-theoretic statement in every characteristic. -/
theorem fpqc_multiple_descent
    {S : Scheme.{u}} {A B Z : Over S}
    [GrpObj A] [GrpObj B] [GrpObj Z] [IsCommMonObj Z]
    (f : A ⟶ B) [IsMonHom f]
    [Flat f.left] [Surjective f.left] [QuasiCompact f.left]
    (g : A ⟶ Z) [IsMonHom g] (n : ℕ)
    (hker : ∀ (T : Over S) (x : T ⟶ A), x ≫ f = 1 → x ^ n = 1) :
    ∃! d : B ⟶ Z, IsMonHom d ∧ f ≫ d = g ^ n := by
  have : EffectiveEpi f := effectiveEpi_over_of_fpqc f
  have : EffectiveEpi (f ⊗ₘ f) := effectiveEpi_tensor_over_of_fpqc f f
  exact exists_unique_multiple_descent f g n hker

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.IsogenyFactorizationIs.IsogenyFactorization
