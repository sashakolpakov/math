import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalCoefficientComponent
import OAI.NumberTheory.PadicHodge.IntegralComparison.Small.PDIntrinsicSymbols

/-! # Principal PD Symbols -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalPDSymbols

noncomputable section

/-! The actual principal localization comparison preserves differential
symbols in the native finite-level model frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (U : X.left.affineOpens)

local notation "W" => WittVector p k
local notation "Q" => Functor.obj (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SmallFrame.functor p k n X Y f hp) U
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Diagram.functor X.left U.val U.property

variable (r : PrincipalFrame.Index X.left U)

abbrev sourceFrame := AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.object p k Y Q r
abbrev targetFrame := (SmallFrame.bigFunctor p k n X Y f hp).obj ((P).obj r)

local instance targetAlgebra : Algebra W (targetFrame p k n X Y f hp U r).ring :=
  (targetFrame p k n X Y f hp U r).base.toAlgebra

omit [IsProper X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem symbol (q : ℕ) (a : (sourceFrame p k n X Y f hp U r).thickening.ring)
    (v : Fin q → (sourceFrame p k n X Y f hp U r).thickening.ring) :
    ((Principal.Comparison.nativePDMap p k n X Y f hp U).f q).app (op r)
        (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol W (sourceFrame p k n X Y f hp U r).thickening.ring
          (RingHom.ker (sourceFrame p k n X Y f hp U r).thickening.reduction)
          (sourceFrame p k n X Y f hp U r).thickening.dividedPowers a v) =
      AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol W (targetFrame p k n X Y f hp U r).ring
        (targetFrame p k n X Y f hp U r).ideal
        (targetFrame p k n X Y f hp U r).dividedPowers
        ((PrincipalFrame.map p k n X Y f hp U r).ambientMap a)
        (fun i => (PrincipalFrame.map p k n X Y f hp U r).ambientMap (v i)) := by
  rw [PrincipalCoefficientComponent.PD.nativePDMap_component]
  change ((PrincipalCoefficientComponent.PD.coordinate p k n X Y f hp U r).f q)
    (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap
      (CommAlgCat.ofHom (PrincipalFrame.map p k n X Y f hp U r).ambientMap)
      (PrincipalFrame.map p k n X Y f hp U r).dp_comp q
      (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol _ _ _ _ a v)) = _
  rw [AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap_symbol]
  exact Small.PDIntrinsicSymbols.Intrinsic.hom_symbol p k Y
    ((SmallFrame.smallFunctor p k n X Y f hp).obj ((P).obj r)) q _ _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalPDSymbols
