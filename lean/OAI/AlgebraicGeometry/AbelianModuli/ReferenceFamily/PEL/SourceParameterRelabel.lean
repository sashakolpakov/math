import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired.PELQuotients
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TotalParameters

/-! # Source Parameter Relabel -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL

noncomputable section

/-! Viewing an existing base through its source map changes only the
recorded structural morphism to the ground field. The actual abelian
schemes, actions, pairings, isogenies, and ordered levels are retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TotalParameters.Construction

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [Field K]
    {s N n : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    {T X : Over (Spec (.of K))}

def Objects.PELObject.overSourceParameter (B : Objects.PELObject P iota N X) (t : X ⟶ T) :
    Objects.PELObject P iota N (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameter T (Over.mk t.left)) where
  polarized := B.polarized
  action := B.action
  rosati := B.rosati
  lieRanks := by
    intro F _ _ j p hp τ
    apply B.lieRanks F j p
    change p ≫ (t.left ≫ T.hom) = _ at hp
    erw [t.w] at hp
    exact hp

def SourceParameterRelabel.pairedPELOverSourceParameter {A : Objects.PELObject P iota N T}
    {B : Objects.PELObject P iota N X} (t : X ⟶ T)
    (f : Paired.PELQuotients.PairedPELQuotient (A.pullback t) B n) :
    Paired.PELQuotients.PairedPELQuotient (A.pullback (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource T (Over.mk t.left)))
      (B.overSourceParameter t) n where
  forward := {
    isogeny := f.forward.isogeny
    etale := f.forward.etale
    polarization := f.forward.polarization
    action := f.forward.action
    marking := f.forward.marking }
  reverse := {
    isogeny := f.reverse.isogeny
    etale := f.reverse.etale
    polarization := f.reverse.polarization
    action := f.reverse.action
    marking := f.reverse.marking }
  forward_reverse := f.forward_reverse
  reverse_forward := f.reverse_forward

theorem SourceParameterRelabel.pairedPELOverSourceParameter_forward_hom {A : Objects.PELObject P iota N T}
    {B : Objects.PELObject P iota N X} (t : X ⟶ T)
    (f : Paired.PELQuotients.PairedPELQuotient (A.pullback t) B n) :
    (SourceParameterRelabel.pairedPELOverSourceParameter t f).forward.isogeny.hom = f.forward.isogeny.hom := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL
