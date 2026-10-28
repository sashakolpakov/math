import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalPDSymbols
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSmallIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.OrdinarySymbols

/-! # Principal Ordinary Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalOrdinaryMap.Ordinary

noncomputable section

/-! The original principal PD complex and the actual ordinary differential
forms on its affine principal opens are canonically isomorphic. -/

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
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.Ring p k n
local notation "Q" => Functor.obj (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SmallFrame.functor p k n X Y f hp) U
local notation "C" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFrame.Index X.left U
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Diagram.functor X.left U.val U.property

def target : CochainComplex (Cᵒᵖ ⥤ ModuleCat W) ℕ :=
  AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) ((P).op ⋙ OrdinaryBaseIso.Ordinary.target p k n X)

def map : Supported.PDComplex.localizedComplex p k Y Q ⟶ target p k n X U :=
  Principal.Comparison.nativePDMap p k n X Y f hp U ≫
    AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) (Functor.whiskerLeft (P).op
      (OrdinaryBaseIso.Ordinary.pdIso p k n X Y f hp).hom)

instance pdTransformation_isIso :
    IsIso (PrincipalFrame.pdTransformation p k n X Y f hp U) := by
  dsimp only [PrincipalFrame.pdTransformation]
  infer_instance

instance pdMap_isIso : IsIso (PrincipalFrame.pdMap p k n X Y f hp U) := by
  let : IsIso (PrincipalFrame.pdTransformation p k n X Y f hp U) :=
    pdTransformation_isIso p k n X Y f hp U
  change IsIso ((PrincipalFrame.sourceIso p k n X Y f hp U).hom ≫
    (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.functor (.up ℕ)).map (PrincipalFrame.pdTransformation p k n X Y f hp U))
  infer_instance

instance nativePDMap_isIso :
    IsIso (Principal.Comparison.nativePDMap p k n X Y f hp U) := by
  dsimp only [Principal.Comparison.nativePDMap]
  infer_instance

instance map_isIso : IsIso (Ordinary.map p k n X Y f hp U) := by
  change IsIso (Principal.Comparison.nativePDMap p k n X Y f hp U ≫
    (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.functor (.up ℕ)).map (Functor.whiskerLeft (P).op
      (OrdinaryBaseIso.Ordinary.pdIso p k n X Y f hp).hom))
  infer_instance

def iso : Supported.PDComplex.localizedComplex p k Y Q ≅ target p k n X U :=
  asIso (Ordinary.map p k n X Y f hp U)

omit [IsProper X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem component (q : ℕ) (r : PrincipalFrame.Index X.left U) :
    ((Ordinary.map p k n X Y f hp U).f q).app (op r) =
      ((Principal.Comparison.nativePDMap p k n X Y f hp U).f q).app (op r) ≫
        ((OrdinaryBaseIso.Ordinary.pdIso p k n X Y f hp).hom.app (op ((P).obj r))).f q := rfl

variable (r : PrincipalFrame.Index X.left U)

local instance truncated : Algebra S Γ(X.left, ((P).obj r).val) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra S X ((P).obj r).val

omit [IsProper X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem symbol (q : ℕ)
    (a : (PrincipalPDSymbols.sourceFrame p k n X Y f hp U r).thickening.ring)
    (v : Fin q → (PrincipalPDSymbols.sourceFrame p k n X Y f hp U r).thickening.ring) :
    ((Ordinary.map p k n X Y f hp U).f q).app (op r)
        (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol W
          (PrincipalPDSymbols.sourceFrame p k n X Y f hp U r).thickening.ring
          (RingHom.ker (PrincipalPDSymbols.sourceFrame p k n X Y f hp U r).thickening.reduction)
          (PrincipalPDSymbols.sourceFrame p k n X Y f hp U r).thickening.dividedPowers a v) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol S Γ(X.left, ((P).obj r).val)
        ((PrincipalFrame.map p k n X Y f hp U r).ambientMap a)
        (fun i => (PrincipalFrame.map p k n X Y f hp U r).ambientMap (v i)) := by
  rw [component]
  change ((OrdinaryBaseIso.Ordinary.pdIso p k n X Y f hp).hom.app (op ((P).obj r))).f q
    (((Principal.Comparison.nativePDMap p k n X Y f hp U).f q).app (op r)
      (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol _ _ _ _ a v)) = _
  erw [PrincipalPDSymbols.symbol p k n X Y f hp U r q a v]
  exact OrdinarySymbols.Ordinary.hom_symbol p k n X Y f hp ((P).obj r) q _ _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalOrdinaryMap.Ordinary
