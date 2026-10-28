import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.Abelian

/-! # Two Step Quotient -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.TwoStepQuotient

noncomputable section

/-! Two successive actual cokernels of the beginning of an exact complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]

def firstQuotientDifferential (S : ShortComplex C) : cokernel S.f ⟶ S.X₃ :=
  cokernel.desc S.f S.g S.zero

theorem firstQuotientDifferential_comp (S : ShortComplex C) :
    cokernel.π S.f ≫ firstQuotientDifferential S = S.g := cokernel.π_desc _ _ _

theorem firstQuotientDifferential_mono (S : ShortComplex C) (hS : S.Exact) :
    Mono (firstQuotientDifferential S) := hS.mono_cokernelDesc

def firstQuotientSequence (S : ShortComplex C) : ShortComplex C := ShortComplex.cokernelSequence S.f

theorem firstQuotientSequence_shortExact (S : ShortComplex C) [Mono S.f] :
    (firstQuotientSequence S).ShortExact := by
  dsimp [firstQuotientSequence, ShortComplex.cokernelSequence]
  exact { exact := ShortComplex.cokernelSequence_exact S.f }

def secondQuotientSequence (S : ShortComplex C) : ShortComplex C :=
  ShortComplex.cokernelSequence (firstQuotientDifferential S)

theorem secondQuotientSequence_shortExact (S : ShortComplex C) (hS : S.Exact) :
    (secondQuotientSequence S).ShortExact := by
  have := firstQuotientDifferential_mono S hS
  dsimp [secondQuotientSequence, ShortComplex.cokernelSequence]
  exact { exact := ShortComplex.cokernelSequence_exact (firstQuotientDifferential S) }

theorem firstQuotientDifferential_next (S : ShortComplex C) {B : C}
    (d : S.X₃ ⟶ B) (hd : S.g ≫ d = 0) : firstQuotientDifferential S ≫ d = 0 := by
  apply (cancel_epi (cokernel.π S.f)).mp
  rw [← Category.assoc, firstQuotientDifferential_comp, comp_zero, hd]

def secondQuotientDifferential (S : ShortComplex C) {B : C}
    (d : S.X₃ ⟶ B) (hd : S.g ≫ d = 0) : cokernel (firstQuotientDifferential S) ⟶ B :=
  cokernel.desc (firstQuotientDifferential S) d (firstQuotientDifferential_next S d hd)

theorem secondQuotientDifferential_comp (S : ShortComplex C) {B : C}
    (d : S.X₃ ⟶ B) (hd : S.g ≫ d = 0) :
    cokernel.π (firstQuotientDifferential S) ≫ secondQuotientDifferential S d hd = d :=
  cokernel.π_desc _ _ _

theorem secondQuotientDifferential_mono (S : ShortComplex C) {B : C}
    (d : S.X₃ ⟶ B) (hd : S.g ≫ d = 0) (he : (ShortComplex.mk S.g d hd).Exact) :
    Mono (secondQuotientDifferential S d hd) := by
  let T := ShortComplex.mk (firstQuotientDifferential S) d (firstQuotientDifferential_next S d hd)
  let φ : ShortComplex.mk S.g d hd ⟶ T := {
    τ₁ := cokernel.π S.f
    τ₂ := 𝟙 _
    τ₃ := 𝟙 _
    comm₁₂ := by simp only [T, firstQuotientDifferential_comp, Category.comp_id]
    comm₂₃ := by simp only [T, Category.id_comp, Category.comp_id] }
  have hφ : Epi φ.τ₁ := inferInstanceAs (Epi (cokernel.π S.f))
  have hφ₂ : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 S.X₃))
  have hφ₃ : Mono φ.τ₃ := inferInstanceAs (Mono (𝟙 B))
  have hT : T.Exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mp he
  exact hT.mono_cokernelDesc

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.TwoStepQuotient
