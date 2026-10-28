import OAI.AlgebraicGeometry.Picard.PoincareBundle.Intrinsic.CechCocycle

/-! # Triple Condition -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Intrinsic.TripleCondition

noncomputable section

/-!
# A named geometric triple-overlap condition for stable affine specialization
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.DescentEquations

/-- The native geometric cocycle on three coordinate pairs. -/
def NativeTriple {A Y Z : Scheme.{u}} {L : A.Modules} {x y : Y ⟶ A}
    (σ : (Scheme.Modules.pullback x).obj L ⟶ (Scheme.Modules.pullback y).obj L)
    (a b c : Z ⟶ A) (p₁₂ p₁₃ p₂₃ : Z ⟶ Y)
    (h₁₂₁ : p₁₂ ≫ x = a) (h₁₂₂ : p₁₂ ≫ y = b)
    (h₁₃₁ : p₁₃ ≫ x = a) (h₁₃₂ : p₁₃ ≫ y = c)
    (h₂₃₁ : p₂₃ ≫ x = b) (h₂₃₂ : p₂₃ ≫ y = c) : Prop :=
  Geometric.DescentEquations.nativePullback σ p₁₂ a b h₁₂₁ h₁₂₂ ≫ Geometric.DescentEquations.nativePullback σ p₂₃ b c h₂₃₁ h₂₃₂ =
    Geometric.DescentEquations.nativePullback σ p₁₃ a c h₁₃₁ h₁₃₂

/-- Ordinary scheme descent data satisfy the native triple-overlap condition. -/
theorem hasTripleCocycle {A B : Scheme.{u}} (f : A ⟶ B)
    (D : Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f))
    {Y Z : Scheme.{u}} (q : Y ⟶ B) (q' : Z ⟶ B)
    (x y : Y ⟶ A) (hx : x ≫ f = q) (hy : y ≫ f = q)
    (a b c : Z ⟶ A) (ha : a ≫ f = q') (hb : b ≫ f = q') (hc : c ≫ f = q')
    (p₁₂ p₁₃ p₂₃ : Z ⟶ Y)
    (h₁₂₁ : p₁₂ ≫ x = a) (h₁₂₂ : p₁₂ ≫ y = b)
    (h₁₃₁ : p₁₃ ≫ x = a) (h₁₃₂ : p₁₃ ≫ y = c)
    (h₂₃₁ : p₂₃ ≫ x = b) (h₂₃₂ : p₂₃ ≫ y = c) :
    NativeTriple (D.hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit) x y hx hy)
      a b c p₁₂ p₁₃ p₂₃ h₁₂₁ h₁₂₂ h₁₃₁ h₁₃₂ h₂₃₁ h₂₃₂ :=
  CechCocycle.triple_cocycle f D q q' x y hx hy a b c ha hb hc
    p₁₂ p₁₃ p₂₃ h₁₂₁ h₁₂₂ h₁₃₁ h₁₃₂ h₂₃₁ h₂₃₂

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Intrinsic.TripleCondition
