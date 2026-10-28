import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSupported.Pushforward
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedRows
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.DeRhamSectionUnit

/-! # Supported Global Data -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedGlobalData

noncomputable section

/-! The actual supported comparison on the pushed native resolution
has the original bounded crystalline value after forgetting support. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (U : X.left.affineOpens)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))

def baseMap : Y.left.toTopCat ⟶ X.left.toTopCat := f.base

abbrev opens := Principal.DeRhamSectionUnit.opens (Truncated.Witt.Ring p k n) X U
abbrev target := ModelSheafComparison.target p k n X Y f I
abbrev family (g : ℕ) (a : Fin g → Γ(X.left, U.val)) :=
  Supported.Comparison.family p k n X U g a

omit [Fintype k] [CharP k p] [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem opens_eq : Supported.OrderedCechPushforward.pulled (baseMap p k n X Y f) (opens p k n X U) =
    Supported.Comparison.opens p k n X Y f U := rfl

omit [Fintype k] [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem target_eq : BoundedSupported.Pushforward.pushed
    (Witt.Crystalline.wittStructureMap p k Y) n I (baseMap p k n X Y f) = target p k n X Y f I := rfl

omit [Fintype k] [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem globalHomologyIso_eq (q : ℕ) : BoundedSupported.Pushforward.globalHomologyIso
    (Witt.Crystalline.wittStructureMap p k Y) n I (baseMap p k n X Y f) q =
    CechIso.ResolutionGlobal.globalHomologyIso p k n X Y f I q := rfl

omit [Fintype k] [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem exactAt_succ (g : ℕ) (a : Fin g → Γ(X.left, U.val)) (q r : ℕ) :
    ((Supported.OrderedCechEdge.bicomplex.{1,0,0,2}
      (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) X.left.toTopCat
      (opens p k n X U) (family p k n X U g a) (target p k n X Y f I)).X q).ExactAt (r+1) :=
  SupportedRows.exactAt_succ p k n X Y f U I g a q r

variable (g : ℕ) (a : Fin g → Γ(X.left, U.val)) (O : X.left.Opens)
  (hO : ∀ i, (opens p k n X U).obj (family p k n X U g a i) ≤ O)
  (hcover : (opens p k n X U).obj (⊤_ (PrincipalFrame.Index X.left U)) ⊓ O ≤
    ⨆ i, (opens p k n X U).obj (family p k n X U g a i))
  (hglobal : (opens p k n X U).obj (⊤_ (PrincipalFrame.Index X.left U)) ⊔ O = ⊤)

def forgetSupport (q : ℕ) :=
  Supported.OrderedCech.Comparison.forgetSupport.{1,0,0,2}
    (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) X.left.toTopCat
    (opens p k n X U) (family p k n X U g a) O (target p k n X Y f I)
    hO hcover (exactAt_succ p k n X Y f U I g a) hglobal q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedGlobalData
