import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Principal
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IncomingRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionSubsite

/-! # Principal Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSections

noncomputable section

/-! The whole principal-open section family factors through the
original incoming crystalline subsite of the fixed special open. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (U : X.left.affineOpens)

local notation "W" => WittVector p k
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "C" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFrame.Index X.left U
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Diagram.functor X.left U.val U.property
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SectionBifunctor.specialOpens p k n X Y f

def opens : C →o Y.left.Opens where
  toFun r := (S).obj ((F).obj r)
  monotone' := by
    intro a b hab
    exact leOfHom ((S).map ((F).map (homOfLE hab)))

omit [Fintype k] [CharP k p] [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem le_chart (r : C) : opens p k n X Y f U r ≤ f ⁻¹ᵁ U.val :=
  leOfHom ((S).map (AffinePrincipal.Diagram.projection X.left U.val U.property r))

abbrev localSections := BoundedOpen.SectionSubsite.localSections (p := p)
  (J := Ideal.span {(p : W)}) (δ := γ) w n (f ⁻¹ᵁ U.val) (opens p k n X Y f U)

def iso : SectionBifunctor.sections p k n X Y f ⋙
    Principal.Comparison.restriction p k n X U ≅
      IncomingRestriction.restriction p k n X Y f U ⋙
        localSections p k n X Y f U :=
  BoundedOpen.SectionSubsite.iso (p := p) (J := Ideal.span {(p : W)}) (δ := γ)
    w n (f ⁻¹ᵁ U.val) (opens p k n X Y f U) (le_chart p k n X Y f U)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSections
