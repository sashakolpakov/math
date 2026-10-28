import OAI.AlgebraicGeometry.DivisorClass.Chern.TwoStepQuotient
import Mathlib.Topology.Sheaves.AddCommGrpCat

/-! # Second Quotient Cocycles -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.SecondQuotientCocycles

noncomputable section

/-! Actual closed sections lift uniquely into the second quotient of a locally exact complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]

theorem secondQuotientDifferential_next (S : ShortComplex C) {B D : C}
    (d : S.X₃ ⟶ B) (hd : S.g ≫ d = 0) (e : B ⟶ D) (he : d ≫ e = 0) :
    TwoStepQuotient.secondQuotientDifferential S d hd ≫ e = 0 := by
  apply (cancel_epi (cokernel.π (TwoStepQuotient.firstQuotientDifferential S))).mp
  rw [← Category.assoc, TwoStepQuotient.secondQuotientDifferential_comp, comp_zero, he]

def secondQuotientCycleSequence (S : ShortComplex C) {B D : C}
    (d : S.X₃ ⟶ B) (hd : S.g ≫ d = 0) (e : B ⟶ D) (he : d ≫ e = 0) : ShortComplex C :=
  ShortComplex.mk (TwoStepQuotient.secondQuotientDifferential S d hd) e (secondQuotientDifferential_next S d hd e he)

theorem secondQuotientCycleSequence_exact (S : ShortComplex C) {B D : C}
    (d : S.X₃ ⟶ B) (hd : S.g ≫ d = 0) (e : B ⟶ D) (he : d ≫ e = 0)
    (hE : (ShortComplex.mk d e he).Exact) : (secondQuotientCycleSequence S d hd e he).Exact := by
  let φ : ShortComplex.mk d e he ⟶ secondQuotientCycleSequence S d hd e he := {
    τ₁ := cokernel.π (TwoStepQuotient.firstQuotientDifferential S)
    τ₂ := 𝟙 _
    τ₃ := 𝟙 _
    comm₁₂ := by simp only [secondQuotientCycleSequence, TwoStepQuotient.secondQuotientDifferential_comp, Category.comp_id]
    comm₂₃ := by simp only [secondQuotientCycleSequence, Category.id_comp, Category.comp_id] }
  have : Epi φ.τ₁ := inferInstanceAs (Epi (cokernel.π (TwoStepQuotient.firstQuotientDifferential S)))
  have : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 B))
  have : Mono φ.τ₃ := inferInstanceAs (Mono (𝟙 D))
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mp hE

theorem sheafSecondQuotient_exists_section {X : TopCat.{0}}
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X))
    {B D : TopCat.Sheaf AddCommGrpCat.{0} X}
    (d : S.X₃ ⟶ B) (hd : S.g ≫ d = 0) (e : B ⟶ D) (he : d ≫ e = 0)
    (hmid : (ShortComplex.mk S.g d hd).Exact) (hlast : (ShortComplex.mk d e he).Exact)
    (U : Opens X) (ω : B.obj.obj (op U)) (hω : e.hom.app (op U) ω = 0) :
    ∃ s : (cokernel (TwoStepQuotient.firstQuotientDifferential S)).obj.obj (op U),
      (TwoStepQuotient.secondQuotientDifferential S d hd).hom.app (op U) s = ω := by
  have hmono : Mono (secondQuotientCycleSequence S d hd e he).f :=
    TwoStepQuotient.secondQuotientDifferential_mono S d hd hmid
  exact TopCat.Sheaf.sections_exact_of_left_exact
    (secondQuotientCycleSequence_exact S d hd e he hlast) hmono ω hω

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.SecondQuotientCocycles
