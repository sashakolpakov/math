import OAI.AlgebraicGeometry.Quotients.FiniteDescent.NormalizedScalar
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence

/-! # Scalar Short -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ScalarShort

noncomputable section

/-! Assemble normalized scalar-extension comparisons on three module
terms into an isomorphism of short complexes. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped ChangeOfRings

universe u

namespace Construction.ScalarShortComplexData

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

theorem square {A B : ModuleCat.{u} R} {C D : ModuleCat.{u} S}
    (p : A ⟶ B) (q : C ⟶ D) (v : A → C) (w : B → D)
    (e : NormalizedScalar.Construction.NormalizedScalarIso.Data f v) (d : NormalizedScalar.Construction.NormalizedScalarIso.Data f w)
    (h : ∀ x, q (v x) = w (p x)) : e.val.hom ≫ q = (ModuleCat.extendScalars f).map p ≫ d.val.hom := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  change q (e.val.hom ((1 : S) ⊗ₜ[R,f] x)) =
    d.val.hom ((ModuleCat.extendScalars f).map p ((1 : S) ⊗ₜ[R,f] x))
  exact (congrArg q (e.property x)).trans ((h x).trans (d.property (p x)).symm)

def iso (C : ShortComplex (ModuleCat.{u} R)) (D : ShortComplex (ModuleCat.{u} S))
    (v₁ : C.X₁ → D.X₁) (v₂ : C.X₂ → D.X₂) (v₃ : C.X₃ → D.X₃)
    (e₁ : NormalizedScalar.Construction.NormalizedScalarIso.Data f v₁) (e₂ : NormalizedScalar.Construction.NormalizedScalarIso.Data f v₂)
    (e₃ : NormalizedScalar.Construction.NormalizedScalarIso.Data f v₃)
    (h₁ : ∀ x, D.f (v₁ x) = v₂ (C.f x)) (h₂ : ∀ x, D.g (v₂ x) = v₃ (C.g x)) :
    C.map (ModuleCat.extendScalars f) ≅ D :=
  ShortComplex.isoMk e₁.val e₂.val e₃.val
    (square f C.f D.f v₁ v₂ e₁ e₂ h₁) (square f C.g D.g v₂ v₃ e₂ e₃ h₂)

end Construction.ScalarShortComplexData

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ScalarShort
