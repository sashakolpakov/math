import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Supported
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Products
import OAI.NumberTheory.PadicHodge.IntegralComparison.FlasqueOrderedRows

/-! # Supported Rows -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedRows

noncomputable section

/-! The actual principal-open supported Čech rows of the original
bounded crystalline injective resolution are exact in every positive
degree. No row-acyclicity assumption is added. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (U : X.left.affineOpens)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))

local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Supported.Comparison.opens p k n X Y f U
local notation "K" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.FlasqueComplex.complex w n I

omit [Fintype k] [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem exactAt_succ (g : ℕ) (a : Fin g → Γ(X.left, U.val)) (q r : ℕ) :
    ((BoundedSupported.Cech.bicomplex w n I G
      (Supported.Comparison.family p k n X U g a)).X q).ExactAt (r + 1) := by
  let V := Supported.Comparison.family p k n X U g a
  let : ∀ (m : ℕ) (t : Fin (m + 1) → ULift (Fin g)),
      PreservesLimit (Discrete.functor (V ∘ t)) G := by
    intro m t
    exact AffinePrincipal.Products.pullback_preserves X.left U.val U.property Y.left f (V ∘ t)
  let : TopCat.Presheaf.IsFlasque (X := Y.left.carrier) (((K).X q).obj) :=
    BoundedOpen.FlasqueComplex.term_flasque w n I q
  exact FlasqueOrderedRows.exactAt_succ.{1,2} R Y.left.carrier G V ((K).X q) r

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedRows
