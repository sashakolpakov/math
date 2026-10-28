import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.DualRefinementMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.IntrinsicDualCoordinates

/-! # Dual Refinement Residue -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.DualRefinementResidue

noncomputable section

/-! A residue after the original right/inverse-left transfer is the
same residue after the literal principal dual transfer. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
  {ι : Type u} [LinearOrder ι] (W : ι → SectionPresheaf.Index U) (q : ℕ)
  (N : X.Modules) {P K T : ChainComplex X.Modules ℕ}
  (l : T ⟶ K) (r : T ⟶ P)
  [IsIso ((PrincipalReference.Concentration.Reference.functor U hU W q).map
    ((Affine.LocalDualInvariance.functor N).map l.op))]
  {L : CochainComplex ((SectionPresheaf.Index U)ᵒᵖ ⥤
    ModuleCat.{u} Γ(X,U)) ℕ}
  (a : Koszul.Comparison.nativeComplex U hU N K ⟶ L)

private theorem apply_after {A : Type*} [Ring A] {P Q T : ModuleCat A}
    {l r : P ⟶ Q} (h : l = r) (f : Q ⟶ T) (y : P) : f (l y) = f (r y) := by
  cases h
  rfl

abbrev apply :=
  apply_after (DualRefinementMap.refinement U hU W q N l r)
    ((Supported.CechHomotopyEquivalence.functor W q).map
      (IntrinsicDualCoordinates.Intrinsic.map U hU N K a))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.DualRefinementResidue
