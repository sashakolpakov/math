import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.SingleEdge
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.CechSingle
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ZeroSections

/-! # Single Edge -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicOrdered.SingleEdge.Intrinsic

noncomputable section

/-! Exact augmentation normalization for the original base-linear
ordered Čech total of a single module sheaf. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X S : Scheme.{u}} (π : X ⟶ S) [X.IsSeparated]
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : iSup U = ⊤)

local notation "F" => OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechComplexFunctor π U
local notation "E" => OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Augmentation.sections π

def augmentation : E ⟶ F ⋙ HomologicalComplex.eval (ModuleCat.{u} Γ(S, ⊤)) (.up ℕ) 0 where
  app M := OrderedCech.Augmentation.map π U M
  naturality _ _ f := OrderedCech.Augmentation.naturality π U f

abbrev edge (M : X.Modules) (c : ℕ) :=
  Functor.SingleEdge.edge F E (augmentation π U)
    (fun M => OrderedCech.Augmentation.map_d π U M hU) M c

variable (M : X.Modules) (c : ℕ)

omit [X.IsSeparated] in
theorem generic_homologyIso (q : ℕ) :
    Functor.SingleTotal.homologyIso F M c q =
      OrderedCech.CechSingle.homologyIso π U M c q := rfl

abbrev columnIso :
    ((OrderedCech.CechSingle.bicomplex π U M c).total (.up ℕ)).homology c ≅
      (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).homology 0 :=
  eqToIso (congrArg (fun q => ((OrderedCech.CechSingle.bicomplex π U M c).total
    (.up ℕ)).homology q) (Nat.zero_add c).symm) ≪≫
      OrderedCech.CechSingle.homologyIso π U M c 0

omit [X.IsSeparated] in
theorem normalization :
    homologyMap (edge π U hU M c) c ≫ (columnIso π U M c).hom =
      (Functor.SingleEdge.sourceIso E M c).hom ≫ (Cech.ZeroSections.iso π U hU M).hom := by
  exact Functor.SingleEdge.normalization F E (augmentation π U)
    (fun M => OrderedCech.Augmentation.map_d π U M hU) M c

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicOrdered.SingleEdge.Intrinsic
