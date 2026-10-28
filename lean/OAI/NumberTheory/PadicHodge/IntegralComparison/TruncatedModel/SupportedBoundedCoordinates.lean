import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedGlobal
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.AdditiveTopFractionData

/-! # Supported Bounded Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedBoundedCoordinates

noncomputable section

/-! The original pushed supported class has the literal native bounded value. -/
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
  (g : ℕ) [SmoothOfRelativeDimension g X.hom] (a : Fin g → Γ(X.left,U.val))

abbrev opens := SupportedGlobalData.opens p k n X U
abbrev family := SupportedGlobalData.family p k n X U g a

variable (O : X.left.Opens)
  (hO : ∀ j, (opens p k n X U).obj (family p k n X U g a j) ≤ O)
  (hcover : (opens p k n X U).obj (⊤_ (PrincipalFrame.Index X.left U)) ⊓ O ≤
    ⨆ j, (opens p k n X U).obj (family p k n X U g a j))
  (hglobal : (opens p k n X U).obj (⊤_ (PrincipalFrame.Index X.left U)) ⊔ O = ⊤)

abbrev map (q : ℕ) := AdditiveTopFractionData.toBounded p k n X Y f U I g a (f ⁻¹ᵁ O)
  (Supported.OrderedCechPushforward.pulled_below f.base (opens p k n X U) (family p k n X U g a) O hO)
  (Supported.OrderedCechPushforward.pulled_cover f.base (opens p k n X U) (family p k n X U g a) O hcover)
  (SupportedRows.exactAt_succ p k n X Y f U I g a)
  (Supported.OrderedCechPushforward.pulled_global f.base (opens p k n X U) O hglobal) q

omit [Fintype k] [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] [SmoothOfRelativeDimension g X.hom] in
theorem comparison (q : ℕ) :
    SupportedGlobalData.forgetSupport p k n X Y f U I g a O hO hcover hglobal q ≫
      (CechIso.ResolutionGlobal.globalHomologyIso p k n X Y f I q).hom =
    map p k n X Y f U I g a O hO hcover hglobal q := by
  have hc := SupportedGlobal.comparison p k n X Y f U I g a O hO hcover hglobal q
  dsimp only [BoundedSupported.Pushforward.toBounded] at hc
  rw [SupportedGlobalData.globalHomologyIso_eq] at hc
  exact hc

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedBoundedCoordinates
