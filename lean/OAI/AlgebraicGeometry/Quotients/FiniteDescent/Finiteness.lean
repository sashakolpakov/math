import Mathlib.RingTheory.Adjoin.Tower
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RingTheory.Flat.Basic

/-! # Finiteness -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.Finiteness.Construction.FinitenessDescent

/-!
# Finiteness through finite extensions with a module retraction

These versions of Artin--Tate do not assume that the base is noetherian.
A surjective linear functional replaces the noetherian-submodule argument.
-/

open _root_.Module

universe u v w

variable {R B A : Type*} [CommRing R] [CommRing B] [CommRing A]
    [Algebra R B] [Algebra B A] [Algebra R A] [IsScalarTower R B A]

/-- Finite type descends through a finite extension admitting a surjective
linear functional, without a noetherian hypothesis on the base. -/
theorem finiteType_of_finite_of_linear_surjective
    [Algebra.FiniteType R A] [Module.Finite B A]
    (p : A →ₗ[B] B) (hp : Function.Surjective p) : Algebra.FiniteType R B := by
  obtain ⟨B₀, hfg, hA⟩ := exists_subalgebra_of_fg R B A
    (Algebra.FiniteType.out) Module.Finite.fg_top
  have : Algebra.FiniteType R B₀ := (Subalgebra.fg_iff_finiteType B₀).mp hfg
  have : Module.Finite B₀ A := ⟨hA⟩
  have : Module.Finite B₀ B := Module.Finite.of_surjective (p.restrictScalars B₀) hp
  exact Algebra.FiniteType.trans (S := B₀) inferInstance inferInstance

/-- A module retraction of a finitely presented module is finitely presented. -/
theorem moduleFinitePresentation_of_retraction
    {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [Module.FinitePresentation R M]
    (p : M →ₗ[R] N) (s : N →ₗ[R] M) (h : p.comp s = LinearMap.id) :
    Module.FinitePresentation R N := by
  have hp : Function.Surjective p := fun n => ⟨s n, DFunLike.congr_fun h n⟩
  apply Module.finitePresentation_of_surjective p hp
  have heq : LinearMap.ker p = LinearMap.range (LinearMap.id - s.comp p) := by
    ext m
    constructor
    · intro hm
      refine ⟨m, ?_⟩
      have hm' : p m = 0 := hm
      simp [hm']
    · rintro ⟨m, rfl⟩
      change p (m - s (p m)) = 0
      rw [map_sub, show p (s (p m)) = p m from DFunLike.congr_fun h (p m), sub_self]
  rw [heq]
  exact Submodule.fg_range _

/-- Finite presentation descends through the same finite extension. -/
theorem finitePresentation_of_finite_of_linear_surjective
    [Algebra.FinitePresentation R A] [Module.Finite B A]
    (p : A →ₗ[B] B) (hp : Function.Surjective p) : Algebra.FinitePresentation R B := by
  have : Algebra.FiniteType R B := finiteType_of_finite_of_linear_surjective p hp
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp this
  let P := MvPolynomial (Fin n) R
  let : Algebra P B := f.toRingHom.toAlgebra
  let : Algebra P A := ((IsScalarTower.toAlgHom R B A).comp f).toRingHom.toAlgebra
  have : IsScalarTower R P B := IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
  have : IsScalarTower R P A := IsScalarTower.of_algebraMap_eq fun r =>
    (((IsScalarTower.toAlgHom R B A).comp f).commutes r).symm
  have : IsScalarTower P B A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Finite P B := RingHom.Finite.of_surjective f.toRingHom hf
  have : Module.Finite P A := Module.Finite.trans B A
  have : Algebra.FinitePresentation P A :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R P A
  have : Module.FinitePresentation P A :=
    Module.FinitePresentation.of_finite_of_finitePresentation P A
  obtain ⟨s, hs⟩ := Module.projective_lifting_property p LinearMap.id hp
  have : Module.FinitePresentation P B := moduleFinitePresentation_of_retraction
    (p.restrictScalars P) (s.restrictScalars P) (by
      ext b
      exact DFunLike.congr_fun hs b)
  have : Algebra.FinitePresentation P B := inferInstance
  exact Algebra.FinitePresentation.trans R P B

/-- The zero algebra is finitely presented over every commutative ring. -/
theorem finitePresentation_of_subsingleton [Subsingleton B] : Algebra.FinitePresentation R B := by
  apply Algebra.FinitePresentation.of_surjective
    (f := Algebra.ofId R B) (fun b => ⟨0, Subsingleton.elim _ _⟩)
  have h : RingHom.ker (Algebra.ofId R B).toRingHom = ⊤ := by
    apply top_unique
    intro x _
    exact Subsingleton.elim _ _
  rw [h]
  exact Ideal.fg_top R

/-- Finite presentation descends through an injective finite free algebra
extension, including the zero-ring case. -/
theorem finitePresentation_of_finite_free
    [Algebra.FinitePresentation R A] [Module.Finite B A] [Module.Free B A]
    (hinj : Function.Injective (algebraMap B A)) : Algebra.FinitePresentation R B := by
  classical
  cases subsingleton_or_nontrivial A with
  | inl h =>
    let : Subsingleton A := h
    let : Subsingleton B := ⟨fun x y => hinj (Subsingleton.elim _ _)⟩
    exact finitePresentation_of_subsingleton
  | inr h =>
    let : Nontrivial A := h
    let b := Module.Free.chooseBasis B A
    obtain ⟨j⟩ := b.index_nonempty
    apply finitePresentation_of_finite_of_linear_surjective (b.coord j)
    intro x
    exact ⟨x • b j, by simp⟩

/-- Flatness over the original base descends through a surjective linear
functional, since it makes the target a module retract of the source. -/
theorem flat_of_linear_surjective [Module.Flat R A]
    (p : A →ₗ[B] B) (hp : Function.Surjective p) : Module.Flat R B := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property p LinearMap.id hp
  exact Module.Flat.of_retract (s.restrictScalars R) (p.restrictScalars R) (by
    ext b
    exact DFunLike.congr_fun hs b)

/-- Flatness descends through an injective free algebra extension. -/
theorem flat_of_free [Module.Flat R A] [Module.Free B A]
    (hinj : Function.Injective (algebraMap B A)) : Module.Flat R B := by
  classical
  cases subsingleton_or_nontrivial A with
  | inl h =>
    let : Subsingleton A := h
    let : Subsingleton B := ⟨fun x y => hinj (Subsingleton.elim _ _)⟩
    exact flat_of_linear_surjective (0 : A →ₗ[B] B) (fun b => ⟨0, Subsingleton.elim _ _⟩)
  | inr h =>
    let : Nontrivial A := h
    let b := Module.Free.chooseBasis B A
    obtain ⟨j⟩ := b.index_nonempty
    exact flat_of_linear_surjective (b.coord j) (fun x => ⟨x • b j, by simp⟩)

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.Finiteness.Construction.FinitenessDescent
