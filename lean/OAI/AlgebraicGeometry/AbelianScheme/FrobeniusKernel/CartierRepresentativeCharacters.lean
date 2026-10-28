import OAI.AlgebraicGeometry.PELModuli.CMPoints.DualityPairing
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.Evaluation

/-! # Cartier Representative Characters -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierRepresentativeCharacters.Construction

noncomputable section

/-! The actual group representative identifies its points with the
original large character functor, retaining evaluation and multiplication. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme} {G : Grp (Over S)}
variable (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G)

def cartierRepresentativeCharacterIso :
    yonedaGrp.obj C.dual ⋙ forget GrpCat ⋙ uliftFunctor.{1, 0} ≅
      PELModuli.CMPoints.DualityPairing.cartierCharacters (yonedaGrp.obj G) :=
  NatIso.ofComponents (fun T => (Equiv.ulift.trans (C.sectionEquiv T.unop).toEquiv).toIso) (by
    intro T U t
    apply ConcreteCategory.hom_ext
    intro x
    exact C.sectionEquiv_natural t.unop x.down)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierRepresentativeCharacters.Construction
