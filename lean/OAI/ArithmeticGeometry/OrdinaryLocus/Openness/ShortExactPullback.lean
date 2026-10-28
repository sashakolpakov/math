import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ExtOneLifting
import Mathlib.CategoryTheory.Abelian.Basic

/-! # Short Exact Pullback -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ShortExactPullback.Construction

noncomputable section

/-! Pulling back an extension along a morphism to its quotient object. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.Abelian

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]
    (S : ShortComplex C) {P : C} (q : P ⟶ S.X₃)

abbrev pullbackShortComplex : ShortComplex C :=
  ShortComplex.mk (pullback.lift (f := S.g) (g := q) S.f (0 : S.X₁ ⟶ P) (by simp))
    (pullback.snd S.g q) (pullback.lift_snd _ _ _)

def pullbackShortComplexMap : pullbackShortComplex S q ⟶ S where
  τ₁ := 𝟙 _
  τ₂ := pullback.fst S.g q
  τ₃ := q
  comm₁₂ := by simp only [Category.id_comp, pullback.lift_fst]
  comm₂₃ := pullback.condition

theorem pullbackShortComplex_shortExact (hS : S.ShortExact) :
    (pullbackShortComplex S q).ShortExact := by
  have hmf : Mono S.f := hS.mono_f
  have heg : Epi S.g := hS.epi_g
  have hmono : Mono (pullbackShortComplex S q).f :=
    mono_of_mono_fac (show (pullbackShortComplex S q).f ≫ pullback.fst S.g q = S.f by
      exact pullback.lift_fst _ _ _)
  have hker : IsLimit (KernelFork.ofι (pullbackShortComplex S q).f
      (pullbackShortComplex S q).zero) := by
    apply KernelFork.IsLimit.ofι'
    intro A a ha
    have hz : (a ≫ pullback.fst S.g q) ≫ S.g = 0 := by
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      change (a ≫ (pullbackShortComplex S q).g) ≫ q = 0
      rw [ha, zero_comp]
    refine ⟨hS.exact.lift (a ≫ pullback.fst S.g q) hz, ?_⟩
    apply pullback.hom_ext
    · change (_ ≫ pullback.lift S.f (0 : S.X₁ ⟶ P) _) ≫ pullback.fst S.g q = _
      rw [Category.assoc, pullback.lift_fst]
      exact hS.exact.lift_f _ hz
    · change (_ ≫ pullback.lift S.f (0 : S.X₁ ⟶ P) _) ≫ pullback.snd S.g q = _
      rw [Category.assoc, pullback.lift_snd, comp_zero]
      exact ha.symm
  exact { exact := ShortComplex.exact_of_f_is_kernel _ hker }

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ShortExactPullback.Construction
