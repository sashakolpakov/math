import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedGlobalData
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSupported.PushforwardIdentity

/-! # Supported Global -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedGlobal

noncomputable section

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

variable (g : ℕ) (a : Fin g → Γ(X.left, U.val)) (O : X.left.Opens)
  (hO : ∀ i, (SupportedGlobalData.opens p k n X U).obj (SupportedGlobalData.family p k n X U g a i) ≤ O)
  (hcover : (SupportedGlobalData.opens p k n X U).obj (⊤_ (PrincipalFrame.Index X.left U)) ⊓ O ≤
    ⨆ i, (SupportedGlobalData.opens p k n X U).obj (SupportedGlobalData.family p k n X U g a i))
  (hglobal : (SupportedGlobalData.opens p k n X U).obj (⊤_ (PrincipalFrame.Index X.left U)) ⊔ O = ⊤)

abbrev comparison (q : ℕ) :=
  BoundedSupported.PushforwardIdentity.comparison (X := X.left.toTopCat)
    (Witt.Crystalline.wittStructureMap p k Y) n I (SupportedGlobalData.baseMap p k n X Y f)
    (SupportedGlobalData.opens p k n X U) (SupportedGlobalData.family p k n X U g a) O hO hcover
    (SupportedGlobalData.exactAt_succ p k n X Y f U I g a) hglobal q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedGlobal
