import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.Additive
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.LinearAlgebra.Quotient.Basic

/-! # Ideal Quotient -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Module.IdealQuotient

noncomputable section

/-! Functorial quotients of the original module complexes by a coefficient ideal. -/

open _root_.CategoryTheory

universe u v

variable (R : Type u) [CommRing R] (I : Ideal R)

def functor : ModuleCat.{v} R ⥤ ModuleCat.{v} R where
  obj M := ModuleCat.of R (M ⧸ (I • ⊤ : Submodule R M))
  map {M N} f := ModuleCat.ofHom (Submodule.mapQ (I • ⊤) (I • ⊤) f.hom
    (Submodule.smul_top_le_comap_smul_top I f.hom))
  map_id M := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := (I • ⊤ : Submodule R M).mkQ_surjective x
    rfl
  map_comp {M N P} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := (I • ⊤ : Submodule R M).mkQ_surjective x
    rfl

instance additive : (functor R I).Additive where
  map_add {M N} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := (I • ⊤ : Submodule R M).mkQ_surjective x
    exact map_add (I • ⊤ : Submodule R N).mkQ (f y) (g y)

instance linear : (functor R I).Linear R where
  map_smul {M N} f r := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := (I • ⊤ : Submodule R M).mkQ_surjective x
    exact map_smul (I • ⊤ : Submodule R N).mkQ r (f y)

def projection : 𝟭 (ModuleCat.{v} R) ⟶ functor R I where
  app M := ModuleCat.ofHom (I • ⊤ : Submodule R M).mkQ
  naturality _ _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

abbrev complex (K : CochainComplex (ModuleCat.{v} R) ℕ) : CochainComplex (ModuleCat.{v} R) ℕ :=
  ((functor R I).mapHomologicalComplex (ComplexShape.up ℕ)).obj K

def complexProjection (K : CochainComplex (ModuleCat.{v} R) ℕ) : K ⟶ complex R I K :=
  ((Functor.mapHomologicalComplexIdIso (ModuleCat.{v} R) (ComplexShape.up ℕ)).inv.app K) ≫
    ((projection R I).mapHomologicalComplex (ComplexShape.up ℕ)).app K

theorem complexProjection_apply (K : CochainComplex (ModuleCat.{v} R) ℕ) (m : ℕ) (x : K.X m) :
    (complexProjection R I K).f m x = Submodule.Quotient.mk x := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Module.IdealQuotient
