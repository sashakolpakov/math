/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SheafificationLocalEquivalences

/-! # Tensor Pairing Locality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.TensorPairingLocality.SheafTensorLocalization

noncomputable section

universe v v' u u'

open _root_.CategoryTheory MonoidalCategory _root_.PresheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {S : Cᵒᵖ ⥤ CommRingCat.{u}}
  {M₁ M₂ N₁ N₂ : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)}
  (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂)
  [Presheaf.IsLocallyInjective J ((toPresheaf _).map f)]
  [Presheaf.IsLocallySurjective J ((toPresheaf _).map f)]
  [Presheaf.IsLocallyInjective J ((toPresheaf _).map g)]
  [Presheaf.IsLocallySurjective J ((toPresheaf _).map g)]
  {P : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)}
  (hP : Presheaf.IsSheaf J P.presheaf) (χ : M₁ ⊗ N₁ ⟶ P)

include hP in
omit [Presheaf.IsLocallySurjective J ((toPresheaf _).map f)]
  [Presheaf.IsLocallySurjective J ((toPresheaf _).map g)] in

lemma chi_app_congr {V : C} (a a' : M₁.obj (Opposite.op V))
    (b b' : N₁.obj (Opposite.op V))
    (hfa : f.app (Opposite.op V) a = f.app (Opposite.op V) a')
    (hgb : g.app (Opposite.op V) b = g.app (Opposite.op V) b') :
    χ.app (Opposite.op V) (a ⊗ₜ b) = χ.app (Opposite.op V) (a' ⊗ₜ b') := by
  have hfa' : ((toPresheaf _).map f).app (Opposite.op V) a =
      ((toPresheaf _).map f).app (Opposite.op V) a' := hfa
  have hgb' : ((toPresheaf _).map g).app (Opposite.op V) b =
      ((toPresheaf _).map g).app (Opposite.op V) b' := hgb
  apply hP.isSeparated _ _ (J.intersection_covering
    (Presheaf.equalizerSieve_mem J ((toPresheaf _).map f) a a' hfa')
    (Presheaf.equalizerSieve_mem J ((toPresheaf _).map g) b b' hgb'))
  rintro W q ⟨hqa, hqb⟩
  have hnat : ∀ x : ((M₁ ⊗ N₁).obj (Opposite.op V) : Type u),
      P.presheaf.map q.op (χ.app (Opposite.op V) x) =
        χ.app (Opposite.op W) ((M₁ ⊗ N₁).map q.op x) :=
    fun x => (CategoryTheory.congr_fun (χ.naturality q.op) x).symm
  erw [hnat, hnat]
  congr 1
  erw [PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul, PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul]
  have hqa' : M₁.map q.op a = M₁.map q.op a' := hqa
  have hqb' : N₁.map q.op b = N₁.map q.op b' := hqb
  rw [hqa', hqb']

def IsPairingSection {U : Cᵒᵖ} (m : M₂.obj U) (n : N₂.obj U)
    (s : P.obj U) : Prop :=
  ∀ ⦃V : C⦄ (p : V ⟶ U.unop) (a : M₁.obj (Opposite.op V)) (b : N₁.obj (Opposite.op V)),
    f.app (Opposite.op V) a = M₂.map p.op m → g.app (Opposite.op V) b = N₂.map p.op n →
    P.map p.op s = χ.app (Opposite.op V) (a ⊗ₜ b)

lemma pom_map_comp (M : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat))
    {X : Cᵒᵖ} {V W : C} (q : W ⟶ V) (p : V ⟶ X.unop) (x : M.obj X) :
    M.map (q ≫ p).op x = M.map q.op (M.map p.op x) :=
  show M.presheaf.map (q ≫ p).op x = M.presheaf.map q.op (M.presheaf.map p.op x) by
    rw [op_comp, M.presheaf.map_comp]
    rfl

lemma pom_napp_map {A B : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)}
    (φ : A ⟶ B) {V W : C} (q : W ⟶ V) (x : A.obj (Opposite.op V)) :
    φ.app (Opposite.op W) (A.map q.op x) = B.map q.op (φ.app (Opposite.op V) x) :=
  CategoryTheory.congr_fun (φ.naturality q.op) x

variable {f g} in
lemma chi_value {V W : C} (q : W ⟶ V) (a : M₁.obj (Opposite.op V))
    (b : N₁.obj (Opposite.op V)) :
    P.presheaf.map q.op (χ.app (Opposite.op V) (a ⊗ₜ b)) =
      χ.app (Opposite.op W) (M₁.map q.op a ⊗ₜ N₁.map q.op b) := by
  refine ((CategoryTheory.congr_fun (χ.naturality q.op) (a ⊗ₜ b)).symm).trans ?_
  exact congrArg (χ.app (Opposite.op W)) (by erw [PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul]; rfl)

variable {f g} in

lemma isPreimagePair_restrict {X : Cᵒᵖ} {m : M₂.obj X} {n : N₂.obj X}
    {V W : C} (q : W ⟶ V) (p : V ⟶ X.unop)
    (a : M₁.obj (Opposite.op V)) (b : N₁.obj (Opposite.op V))
    (ha : f.app (Opposite.op V) a = M₂.map p.op m)
    (hb : g.app (Opposite.op V) b = N₂.map p.op n) :
    f.app (Opposite.op W) (M₁.map q.op a) = M₂.map (q ≫ p).op m ∧
      g.app (Opposite.op W) (N₁.map q.op b) = N₂.map (q ≫ p).op n :=
  ⟨by rw [pom_napp_map f q a, ha, ← pom_map_comp],
    by rw [pom_napp_map g q b, hb, ← pom_map_comp]⟩

variable {f g} in
include hP in
omit [Presheaf.IsLocallyInjective J ((toPresheaf _).map f)]
  [Presheaf.IsLocallyInjective J ((toPresheaf _).map g)] in
lemma isPairingSection_unique {U : Cᵒᵖ} {m : M₂.obj U} {n : N₂.obj U}
    {s s' : P.obj U} (hs : IsPairingSection f g χ m n s)
    (hs' : IsPairingSection f g χ m n s') : s = s' := by
  apply hP.isSeparated _ _ (J.intersection_covering
    (Presheaf.imageSieve_mem J ((toPresheaf _).map f) m)
    (Presheaf.imageSieve_mem J ((toPresheaf _).map g) n))
  rintro V p ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  have ha' : f.app (Opposite.op V) a = M₂.map p.op m := ha
  have hb' : g.app (Opposite.op V) b = N₂.map p.op n := hb
  exact (hs p a b ha' hb').trans (hs' p a b ha' hb').symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.TensorPairingLocality.SheafTensorLocalization
