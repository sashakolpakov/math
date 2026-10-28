import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.TerminalScalars
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.AtOne

/-! # Terminal Scalars -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.TerminalScalars

noncomputable section

/-! The terminal object of the genuine principal-open diagram has
exactly the original sections. In particular, the literal scalar map
in its dual Koszul complex is invertible. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf
variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)

include hU in
theorem open_eq : SectionPresheaf.openSubset U (⊤_ (SectionPresheaf.Index U)) = U := by
  apply le_antisymm (X.basicOpen_le _)
  exact (AtOne.open_eq U).symm.le.trans
    ((AffinePrincipal.Diagram.functor X U hU).map
      (terminal.from (AtOne.object U))).le

include hU in
theorem inclusion_isIso : IsIso (SectionPresheaf.inclusion U (⊤_ (SectionPresheaf.Index U))) := by
  have he : SectionPresheaf.inclusion U (⊤_ (SectionPresheaf.Index U)) = eqToHom (open_eq U hU) := Subsingleton.elim _ _
  rw [he]
  infer_instance

theorem bijective : Function.Bijective
    (algebraMap Γ(X, U) ((SectionPresheaf.rings U hU).obj (op (⊤_ (SectionPresheaf.Index U))))) := by
  let := inclusion_isIso U hU
  exact ConcreteCategory.bijective_of_isIso (X.presheaf.map (SectionPresheaf.inclusion U (⊤_ (SectionPresheaf.Index U))).op)

instance scalarsMap_isIso {c : ℕ} (s : Fin c → Γ(X, U)) :
    IsIso (KoszulPartial.CanonicalMap.scalarsMap Γ(X, U) (SectionPresheaf.rings U hU) s) :=
  Koszul.TerminalScalars.isIso Γ(X, U) (SectionPresheaf.rings U hU) s (bijective U hU)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.TerminalScalars
