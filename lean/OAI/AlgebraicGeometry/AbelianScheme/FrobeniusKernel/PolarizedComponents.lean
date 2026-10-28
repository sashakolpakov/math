import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.Iso

/-! # Polarized Components -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PolarizedComponents.Construction

noncomputable section

/-! Abelian components of a polarized base-change comparison, with the
source abelian scheme and integral action written explicitly. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E : Type} [Field E] {g N : ℕ} {δ : Fin g → ℕ} {S T : Scheme}

structure EquivariantAbelianIso (A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
    (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) B) where
  abelian : A.scheme ≅ B.scheme
  preservesGroup : IsMonHom abelian.hom
  action : ∀ a : NumberField.RingOfIntegers E,
    ρ.map a ≫ abelian.hom = abelian.hom ≫ σ.map a

variable (A : PELModuli.IntegralModel.PEL.Has.PolarizedActionData E g δ N S)
variable (B : PELModuli.IntegralModel.PEL.Has.PolarizedActionData E g δ N T) (f : T ⟶ S)
variable (e : PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso (A.pullback f) B)

def polarizedBaseChangeAbelianComparison :
    EquivariantAbelianIso (A.polarized.abelian.pullback f) B.polarized.abelian
      (A.action.pullback f) B.action where
  abelian := e.polarized.abelian
  preservesGroup := e.polarized.abelianGroup
  action := e.action

theorem polarizedBaseChangeAbelianComparison_abelian :
    (polarizedBaseChangeAbelianComparison A B f e).abelian = e.polarized.abelian := rfl

def polarizedBaseChangeAbelianIso : (A.polarized.abelian.pullback f).scheme ≅
    B.polarized.abelian.scheme := e.polarized.abelian

instance polarizedBaseChangeAbelianIso_isMonHom :
    IsMonHom (polarizedBaseChangeAbelianIso A B f e).hom :=
  e.polarized.abelianGroup

theorem polarizedBaseChangeAbelianIso_action (a : NumberField.RingOfIntegers E) :
    (A.action.pullback f).map a ≫ (polarizedBaseChangeAbelianIso A B f e).hom =
      (polarizedBaseChangeAbelianIso A B f e).hom ≫ B.action.map a :=
  e.action a

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PolarizedComponents.Construction
