import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Duality Descent -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Trace.DualityDescent

noncomputable section

/-! A trace-induced pairing is determined on coproducts and cokernels
by its values on the presenting objects. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v u' v'

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (F : C ⥤ D) {ω : C} {T : D} (τ : F.obj ω ⟶ T)

def pairingMap (M : C) : (M ⟶ ω) → (F.obj M ⟶ T) := fun f => F.map f ≫ τ

theorem pairingMap_comp {M N : C} (f : M ⟶ N) (g : N ⟶ ω) :
    pairingMap F τ M (f ≫ g) = F.map f ≫ pairingMap F τ N g := by
  change F.map (f ≫ g) ≫ τ = F.map f ≫ F.map g ≫ τ
  rw [F.map_comp, Category.assoc]

theorem coproduct_bijective {ι : Type*} (M : ι → C) (c : Cofan M)
    (hc : IsColimit c) [PreservesColimit (Discrete.functor M) F]
    (hM : ∀ i, Function.Bijective (pairingMap F τ (M i))) :
    Function.Bijective (pairingMap F τ c.pt) := by
  classical
  constructor
  · intro f g hfg
    apply hc.hom_ext
    intro i
    apply (hM i.as).1
    rw [pairingMap_comp, pairingMap_comp, hfg]
  · intro l
    choose f hf using fun i => (hM i).2 (F.map (c.inj i) ≫ l)
    let a := hc.desc (Cofan.mk ω f)
    refine ⟨a, ?_⟩
    apply (isColimitOfPreserves F hc).hom_ext
    intro i
    change F.map (c.inj i.as) ≫ pairingMap F τ c.pt a = F.map (c.inj i.as) ≫ l
    exact (pairingMap_comp F τ (c.inj i.as) a).symm.trans
      ((congrArg (pairingMap F τ (M i.as)) (hc.fac (Cofan.mk ω f) i)).trans (hf i.as))

variable [Abelian C] [HasZeroMorphisms D] [F.PreservesZeroMorphisms]

theorem cokernel_bijective (S : ShortComplex C) (hS : S.Exact) [Epi S.g] [Epi (F.map S.g)]
    (h₁ : Function.Injective (pairingMap F τ S.X₁))
    (h₂ : Function.Bijective (pairingMap F τ S.X₂)) :
    Function.Bijective (pairingMap F τ S.X₃) := by
  constructor
  · intro f g hfg
    apply (cancel_epi S.g).mp
    apply h₂.1
    rw [pairingMap_comp, pairingMap_comp, hfg]
  · intro l
    obtain ⟨f, hf⟩ := h₂.2 (F.map S.g ≫ l)
    have hz : S.f ≫ f = 0 := by
      apply h₁
      rw [pairingMap_comp, hf, ← Category.assoc, ← F.map_comp, S.zero, F.map_zero,
        zero_comp]
      change 0 = F.map (0 : S.X₁ ⟶ ω) ≫ τ
      rw [F.map_zero, zero_comp]
    refine ⟨hS.desc f hz, ?_⟩
    apply (cancel_epi (F.map S.g)).mp
    exact (pairingMap_comp F τ S.g (hS.desc f hz)).symm.trans
      ((congrArg (pairingMap F τ S.X₂) (hS.g_desc f hz)).trans hf)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Trace.DualityDescent
