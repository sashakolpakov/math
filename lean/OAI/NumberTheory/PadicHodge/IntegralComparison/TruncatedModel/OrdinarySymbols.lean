import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.OrdinaryBaseIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.FrameComplexSymbols
import OAI.NumberTheory.PadicHodge.IntegralComparison.PD.WeightedResidueFormula

/-! # Ordinary Symbols -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.OrdinarySymbols.Ordinary

noncomputable section

/-! Exact symbols through the original finite-model ordinary comparison.
The inverse sends the literal fractional numerator to its weighted
logarithmic PD form. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))) [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of k))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))

local notation "W" => WittVector p k
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.Ring p k n
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalComplex.Comparison.frames p k n X Y f hp

variable (U : X.left.affineOpens)

local instance truncated : Algebra S Γ(X.left, U.val) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra S X U.val
local instance witt : Algebra W Γ(X.left, U.val) :=
  Truncated.SmoothFrame.Complex.wittAlgebra p k n Γ(X.left, U.val)
local instance tower : IsScalarTower W S Γ(X.left, U.val) := IsScalarTower.of_algebraMap_eq' rfl

abbrev frame := ((H).obj (op U)).unop

theorem hom_symbol (g : ℕ) (a : Γ(X.left, U.val)) (v : Fin g → Γ(X.left, U.val)) :
    ((OrdinaryBaseIso.Ordinary.pdIso p k n X Y f hp).hom.app (op U)).f g
        (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol W Γ(X.left, U.val) (frame p k n X Y f hp U).ideal
          (frame p k n X Y f hp U).dividedPowers a v) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol S Γ(X.left, U.val) a v := by
  let e := PrincipalComplex.Comparison.iso p k n X Y f hp
  let d := GeometricComparison.SurjectiveBase.SurjectiveBaseDeRham.iso W S Γ(X.left, U.val) Ideal.Quotient.mk_surjective
  change d.hom.f g ((e.hom.app (op U)).f g _) = _
  exact (congrArg (fun z : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form W Γ(X.left, U.val) g => d.hom.f g z)
    (Principal.FrameComplexSymbols.hom_symbol (p : W) γ w H
      (PrincipalComplex.Comparison.ideal_generated p k n X Y f hp) (op U) g a v)).trans
      (OrdinaryBaseQuotient.Ordinary.formsEquiv_symbol W S Γ(X.left, U.val)
        Ideal.Quotient.mk_surjective g a v)

theorem inverse_symbol (g : ℕ) (a : Γ(X.left, U.val)) (v : Fin g → Γ(X.left, U.val)) :
    ((OrdinaryBaseIso.Ordinary.pdIso p k n X Y f hp).inv.app (op U)).f g
        (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol S Γ(X.left, U.val) a v) =
      AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol W Γ(X.left, U.val) (frame p k n X Y f hp U).ideal
        (frame p k n X Y f hp U).dividedPowers a v := by
  let e := (HomologicalComplex.Hom.isoApp
    ((OrdinaryBaseIso.Ordinary.pdIso p k n X Y f hp).app (op U)) g).toLinearEquiv
  exact (LinearEquiv.symm_apply_eq e).mpr (hom_symbol p k n X Y f hp U g a v).symm

theorem inverse_fraction (g : ℕ) (v : Fin g → Γ(X.left, U.val)ˣ) (r : WittVector p k) :
    ((OrdinaryBaseIso.Ordinary.pdIso p k n X Y f hp).inv.app (op U)).f g
        (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol S Γ(X.left, U.val)
          (algebraMap W Γ(X.left, U.val) r * (↑((∏ i, v i)⁻¹) : Γ(X.left, U.val)))
          (fun i => (v i : Γ(X.left, U.val)))) =
      r • PD.LogarithmicWedges.Forms.logarithmicWedge W Γ(X.left, U.val)
        (frame p k n X Y f hp U).ideal (frame p k n X Y f hp U).dividedPowers g v :=
  (inverse_symbol p k n X Y f hp U g _ _).trans
    (PD.WeightedResidueFormula.LogarithmicForms.scalar_logarithmicWedge_symbol W Γ(X.left, U.val)
      (frame p k n X Y f hp U).ideal (frame p k n X Y f hp U).dividedPowers g v r).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.OrdinarySymbols.Ordinary
