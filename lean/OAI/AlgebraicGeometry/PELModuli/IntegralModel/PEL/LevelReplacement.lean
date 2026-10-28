import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.Iso
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.Transport

/-! # Level Replacement -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL

noncomputable section

/-! Replacing a level on the same polarized action data, with the
actual isomorphism and its underlying abelian map retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {S : Scheme.{0}} {g L N : ℕ} {δ : Fin g → ℕ}

def Has.PolarizedActionData.withLevel (A : Has.PolarizedActionData E g δ N S)
    (β : A.polarized.abelian.FullLevel L) : Has.PolarizedActionData E g δ L S :=
  ⟨{ A.polarized with level := β }, A.action⟩

def Iso.PolarizedActionIso.withLevel {A B : Has.PolarizedActionData E g δ N S}
    (e : Iso.PolarizedActionIso A B) (α : A.polarized.abelian.FullLevel L)
    (β : B.polarized.abelian.FullLevel L) (h : α.transport e.polarized.abelian = β) :
    Iso.PolarizedActionIso (A.withLevel α) (B.withLevel β) where
  polarized := {
    abelian := e.polarized.abelian
    dual := e.polarized.dual
    abelianGroup := e.polarized.abelianGroup
    dualGroup := e.polarized.dualGroup
    polarization := e.polarized.polarization
    poincare := e.polarized.poincare
    level := fun V c => congrArg
      (fun γ : B.polarized.abelian.FullLevel L => (γ.hom.app (.op V) c).val) h }
  action := e.action

omit [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E] in
theorem Iso.PolarizedActionIso.withLevel_abelian {A B : Has.PolarizedActionData E g δ N S}
    (e : Iso.PolarizedActionIso A B) (α : A.polarized.abelian.FullLevel L)
    (β : B.polarized.abelian.FullLevel L) (h : α.transport e.polarized.abelian = β) :
    (e.withLevel α β h).polarized.abelian = e.polarized.abelian := rfl

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL
