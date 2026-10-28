import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSections

/-! # Principal Functors -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFunctors

noncomputable section

/-! Explicit domain and codomain presentations for the four actual
native section functors used in local comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (V : X.left.affineOpens)

local notation "W" => WittVector p k
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := W)
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.ModuleSheaf (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n

def sections : A ⥤ X.left.affineOpensᵒᵖ ⥤ ModuleCat.{2} R :=
  SectionBifunctor.sections p k n X Y f

def principalRestriction : (X.left.affineOpensᵒᵖ ⥤ ModuleCat.{2} R) ⥤
    (PrincipalFrame.Index X.left V)ᵒᵖ ⥤ ModuleCat.{2} R :=
  Principal.Comparison.restriction p k n X V

def incomingRestriction : A ⥤ BoundedOpen.Subsite.ModuleSheaf
    (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w (f ⁻¹ᵁ V.val).ι n :=
  IncomingRestriction.restriction p k n X Y f V

def localSections : BoundedOpen.Subsite.ModuleSheaf
    (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w (f ⁻¹ᵁ V.val).ι n ⥤
      (PrincipalFrame.Index X.left V)ᵒᵖ ⥤ ModuleCat.{2} R :=
  PrincipalSections.localSections p k n X Y f V

instance sections_additive : (sections p k n X Y f).Additive := by
  dsimp only [sections]
  infer_instance
instance principalRestriction_additive : (principalRestriction p k n X V).Additive := by
  dsimp only [principalRestriction]
  infer_instance
instance incomingRestriction_additive : (incomingRestriction p k n X Y f V).Additive := by
  dsimp only [incomingRestriction]
  infer_instance
instance localSections_additive : (localSections p k n X Y f V).Additive := by
  dsimp only [localSections]
  infer_instance

def iso : sections p k n X Y f ⋙ principalRestriction p k n X V ≅
    incomingRestriction p k n X Y f V ⋙ localSections p k n X Y f V :=
  PrincipalSections.iso p k n X Y f V

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFunctors
