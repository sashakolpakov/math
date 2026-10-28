/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SheafificationLocalEquivalences

/-! # Tensor Local Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.TensorLocalMaps.SheafTensorLocalization

noncomputable section

/-!
Tensoring local surjections remains locally surjective, and maps into sheaves are detected after
tensoring local surjections.

## Provenance

The declarations in this file are adapted from AINTLIB's
`projects/ModularCurves/ModularCurves/ForMathlib/SheafOfModulesMonoidal.lean`.
-/

universe v v' u u'

open _root_.CategoryTheory MonoidalCategory _root_.PresheafOfModules

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{u}} {R : Sheaf J RingCat.{u}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}] [HasWeakSheafify J AddCommGrpCat.{v}]

variable {S : Cᵒᵖ ⥤ CommRingCat.{u}}
  {M₁ M₂ N₁ N₂ : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)}

omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J AddCommGrpCat] in
/-- The locally-surjective half of the [GAP1-W-MONO] tensor-stability leaf: the tensor
product of locally surjective morphisms of presheaves of modules is locally surjective.
Sections of the tensor presheaf are finite sums of simple tensors; each factor is
locally hit, and the finitely many image sieves intersect to a covering sieve. -/
lemma isLocallySurjective_tensorHom (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂)
    [Presheaf.IsLocallySurjective J ((toPresheaf _).map f)]
    [Presheaf.IsLocallySurjective J ((toPresheaf _).map g)] :
    Presheaf.IsLocallySurjective J ((toPresheaf _).map (f ⊗ₘ g)) := by
  constructor
  intro U t
  induction t using TensorProduct.inductionOn with
  | tmul m n =>
      refine J.superset_covering ?_ (J.intersection_covering
        (Presheaf.imageSieve_mem J ((toPresheaf _).map f) m)
        (Presheaf.imageSieve_mem J ((toPresheaf _).map g) n))
      rintro V p ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      refine ⟨a ⊗ₜ b, ?_⟩
      have ha' : f.app (Opposite.op V) a = M₂.map p.op m := ha
      have hb' : g.app (Opposite.op V) b = N₂.map p.op n := hb
      show (f ⊗ₘ g).app (Opposite.op V) (a ⊗ₜ b) = (M₂ ⊗ N₂).map p.op (m ⊗ₜ n)
      erw [PresheafOfModulesOfCommRing.Monoidal.tensorHom_app, ModuleCat.MonoidalCategory.tensorHom_tmul,
        PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul]
      rw [ha', hb']
      rfl
  | add t₁ t₂ h₁ h₂ =>
      refine J.superset_covering ?_ (J.intersection_covering h₁ h₂)
      rintro V p ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩
      refine ⟨x₁ + x₂, ?_⟩
      have hx₁' : (f ⊗ₘ g).app (Opposite.op V) x₁ = (M₂ ⊗ N₂).map p.op t₁ := hx₁
      have hx₂' : (f ⊗ₘ g).app (Opposite.op V) x₂ = (M₂ ⊗ N₂).map p.op t₂ := hx₂
      show (f ⊗ₘ g).app (Opposite.op V) (x₁ + x₂) = (M₂ ⊗ N₂).map p.op (t₁ + t₂)
      erw [map_add, map_add]
      rw [hx₁', hx₂']
      rfl

omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J AddCommGrpCat] in
/-- **([W-MONO-inj])** Precomposition with the tensor of locally surjective morphisms
is injective on morphisms into a presheaf of modules whose underlying presheaf is a
sheaf: two maps out of the tensor agreeing after `f ⊗ₘ g` agree on simple tensors
locally, hence agree by separatedness. -/
theorem tensorHom_precomp_injective (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂)
    [Presheaf.IsLocallySurjective J ((toPresheaf _).map f)]
    [Presheaf.IsLocallySurjective J ((toPresheaf _).map g)]
    {P : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)}
    (hP : Presheaf.IsSheaf J P.presheaf) :
    Function.Injective (fun (ψ : M₂ ⊗ N₂ ⟶ P) => (f ⊗ₘ g) ≫ ψ) := by
  intro ψ₁ ψ₂ h
  refine hom_ext (fun U => ?_)
  ext t
  induction t using TensorProduct.inductionOn with
  | tmul m n =>
      have key : ∀ (ψ : M₂ ⊗ N₂ ⟶ P) {V : C} (p : V ⟶ U.unop)
          (a : M₁.obj (Opposite.op V)) (b : N₁.obj (Opposite.op V))
          (ha : f.app (Opposite.op V) a = M₂.map p.op m)
          (hb : g.app (Opposite.op V) b = N₂.map p.op n),
          P.map p.op (ψ.app U (m ⊗ₜ n)) =
            ((f ⊗ₘ g) ≫ ψ).app (Opposite.op V) (a ⊗ₜ b) := by
        intro ψ V p a b ha hb
        have hnat : ∀ x, P.map p.op (ψ.app U x) =
            ψ.app (Opposite.op V) ((M₂ ⊗ N₂).map p.op x) :=
          fun x => (CategoryTheory.congr_fun (ψ.naturality p.op) x).symm
        have hres : (M₂ ⊗ N₂).map p.op (m ⊗ₜ n) =
            (f ⊗ₘ g).app (Opposite.op V) (a ⊗ₜ b) := by
          erw [PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul, PresheafOfModulesOfCommRing.Monoidal.tensorHom_app,
            ModuleCat.MonoidalCategory.tensorHom_tmul]
          rw [ha, hb]
          rfl
        exact (hnat (m ⊗ₜ n)).trans (congrArg (ψ.app (Opposite.op V)) hres)
      obtain ⟨U⟩ := U
      apply hP.isSeparated _ _ (J.intersection_covering
        (Presheaf.imageSieve_mem J ((toPresheaf _).map f) m)
        (Presheaf.imageSieve_mem J ((toPresheaf _).map g) n))
      rintro V p ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      have ha' : f.app (Opposite.op V) a = M₂.map p.op m := ha
      have hb' : g.app (Opposite.op V) b = N₂.map p.op n := hb
      exact (key ψ₁ p a b ha' hb').trans ((congrArg (fun φ => φ.app (Opposite.op V)
        (a ⊗ₜ b)) h).trans (key ψ₂ p a b ha' hb').symm)
  | add s t hs ht =>
      erw [map_add, map_add]
      rw [hs, ht]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.TensorLocalMaps.SheafTensorLocalization
