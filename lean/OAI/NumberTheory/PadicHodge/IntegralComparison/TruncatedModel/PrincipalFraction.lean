import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalOrdinaryMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Residue

/-! # Principal Fraction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFraction

noncomputable section

/-! The full principal-intersection coefficient of the original PD residue
is the literal fractional differential form on the actual affine open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (U : X.left.affineOpens) (g : ℕ) (a : Fin g → Γ(X.left, U.val))

local notation "W" => WittVector p k
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.Ring p k n
local notation "Q" => Functor.obj (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SmallFrame.functor p k n X Y f hp) U
local notation "t" => OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.PDComplex.topCoefficient p k Y Q g a
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Diagram.functor X.left U.val U.property

def topOpen : X.left.affineOpens := (P).obj t

def coordinateUnit (i : Fin g) : Γ(X.left, (topOpen p k n X Y f hp U g a).val)ˣ :=
  Units.map (PrincipalFrame.map p k n X Y f hp U t).ambientMap.toMonoidHom
    (Supported.PDComplex.coordinateUnit p k Y Q g a i)

omit [IsProper X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem coordinateUnit_val (i : Fin g) :
    (coordinateUnit p k n X Y f hp U g a i : Γ(X.left, (topOpen p k n X Y f hp U g a).val)) =
      (X.left.presheaf.map
        (homOfLE (leOfHom (AffinePrincipal.Diagram.projection X.left U.val U.property t))).op).hom (a i) := by
  change (PrincipalFrame.map p k n X Y f hp U t).ambientMap
    (Units.val (Supported.PDComplex.coordinateUnit p k Y Q g a i)) = _
  erw [Supported.PDComplex.coordinateUnit_val]
  have h := congrArg (fun m => m.ambientMap (a i))
    (PrincipalFrame.map_projection p k n X Y f hp U t)
  exact h.trans (SmallFrame.map_ambient p k n X Y f hp
    (AffinePrincipal.Diagram.projection X.left U.val U.property t) (a i))

local instance truncated : Algebra S Γ(X.left, (topOpen p k n X Y f hp U g a).val) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra S X (topOpen p k n X Y f hp U g a).val
local instance witt : Algebra W Γ(X.left, (topOpen p k n X Y f hp U g a).val) :=
  Truncated.SmoothFrame.Complex.wittAlgebra p k n Γ(X.left, (topOpen p k n X Y f hp U g a).val)

def fraction (r : WittVector p k) :
    ((PrincipalOrdinaryMap.Ordinary.target p k n X U).X g).obj (op t) :=
  AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol S Γ(X.left, (topOpen p k n X Y f hp U g a).val)
    (algebraMap W Γ(X.left, (topOpen p k n X Y f hp U g a).val) r *
      (↑((∏ i, coordinateUnit p k n X Y f hp U g a i)⁻¹) :
        Γ(X.left, (topOpen p k n X Y f hp U g a).val)))
    (fun i => (coordinateUnit p k n X Y f hp U g a i :
      Γ(X.left, (topOpen p k n X Y f hp U g a).val)))

omit [IsProper X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem map_weightedForm (r : WittVector p k) :
    ((PrincipalOrdinaryMap.Ordinary.map p k n X Y f hp U).f g).app (op t)
        (r • Supported.PDComplex.logarithmicForm p k Y Q g a) =
      fraction p k n X Y f hp U g a r := by
  change ((PrincipalOrdinaryMap.Ordinary.map p k n X Y f hp U).f g).app (op t)
    (r • PD.LogarithmicWedges.Forms.logarithmicWedge _ _ _ _ g _) = _
  rw [PD.WeightedResidueFormula.LogarithmicForms.scalar_logarithmicWedge_symbol]
  erw [PrincipalOrdinaryMap.Ordinary.symbol p k n X Y f hp U t g]
  let φ := (PrincipalFrame.map p k n X Y f hp U t).ambientMap
  have hu : Units.map φ.toMonoidHom
        ((∏ i, Supported.PDComplex.coordinateUnit p k Y Q g a i)⁻¹) =
      (∏ i, Units.map φ.toMonoidHom
        (Supported.PDComplex.coordinateUnit p k Y Q g a i))⁻¹ := by
    simp only [map_inv, map_prod]
  have hc := congrArg Units.val hu
  change φ (Units.val ((∏ i, Supported.PDComplex.coordinateUnit p k Y Q g a i)⁻¹)) =
    (↑((∏ i, coordinateUnit p k n X Y f hp U g a i)⁻¹) :
      Γ(X.left, (topOpen p k n X Y f hp U g a).val)) at hc
  change AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol S Γ(X.left, (topOpen p k n X Y f hp U g a).val)
    (φ (algebraMap W (Supported.PDComplex.topFrame p k Y Q g a).thickening.ring r *
      Units.val ((∏ i, Supported.PDComplex.coordinateUnit p k Y Q g a i)⁻¹)))
    (fun i => φ (Units.val (Supported.PDComplex.coordinateUnit p k Y Q g a i))) = _
  erw [map_mul, φ.commutes, hc]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFraction
