import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # Mapped Monoid Hom Equations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MappedMonoidHomEquations

noncomputable section

/-! A strong monoidal functor turns the two monoid-homomorphism equations into exactly the equations for its mapped morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

theorem mappedMonoidHom_one_iff {S T : Scheme.{u}} (F : Over S ⥤ Over T) [F.Monoidal]
    {X Y : Over S} [MonObj X] [MonObj Y] (f : X ⟶ Y) :
    η[F.obj X] ≫ F.map f = η[F.obj Y] ↔ F.map (η[X] ≫ f) = F.map η[Y] := by
  change (Functor.LaxMonoidal.ε F ≫ F.map η[X]) ≫ F.map f =
    Functor.LaxMonoidal.ε F ≫ F.map η[Y] ↔ _
  rw [Category.assoc, ← F.map_comp, cancel_epi]

theorem mappedMonoidHom_mul_iff {S T : Scheme.{u}} (F : Over S ⥤ Over T) [F.Monoidal]
    {X Y : Over S} [MonObj X] [MonObj Y] (f : X ⟶ Y) :
    μ[F.obj X] ≫ F.map f = (F.map f ⊗ₘ F.map f) ≫ μ[F.obj Y] ↔
      F.map (μ[X] ≫ f) = F.map ((f ⊗ₘ f) ≫ μ[Y]) := by
  change (Functor.LaxMonoidal.μ F X X ≫ F.map μ[X]) ≫ F.map f =
    (F.map f ⊗ₘ F.map f) ≫ (Functor.LaxMonoidal.μ F Y Y ≫ F.map μ[Y]) ↔ _
  rw [Category.assoc, Functor.LaxMonoidal.μ_natural_assoc, ← F.map_comp, ← F.map_comp, cancel_epi]

theorem mappedMonoidHom_iff {S T : Scheme.{u}} (F : Over S ⥤ Over T) [F.Monoidal]
    {X Y : Over S} [MonObj X] [MonObj Y] (f : X ⟶ Y) :
    IsMonHom (F.map f) ↔
      F.map (η[X] ≫ f) = F.map η[Y] ∧ F.map (μ[X] ≫ f) = F.map ((f ⊗ₘ f) ≫ μ[Y]) := by
  constructor
  · intro h
    exact ⟨(mappedMonoidHom_one_iff F f).mp h.one_hom, (mappedMonoidHom_mul_iff F f).mp h.mul_hom⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨(mappedMonoidHom_one_iff F f).mpr h₁, (mappedMonoidHom_mul_iff F f).mpr h₂⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MappedMonoidHomEquations
