import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Bundles
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles

/-! # Line Class Comparison -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LineClassComparison.Construction

noncomputable section

/-! PoincareBundle and HilbertConstruction use the same actual locally free rank-one sheaves.
Their line-class functors are canonically isomorphic, preserving pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles

universe u

def e45LineBundleToHilbertConstruction {X : Scheme.{u}} (L : Picard.PoincareBundle.Line.Bundles.LineBundle X) : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X :=
  ⟨L.sheaf, L.isLine⟩

def e33LineBundleToPoincareBundle {X : Scheme.{u}} (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) : Picard.PoincareBundle.Line.Bundles.LineBundle X :=
  ⟨L.sheaf, L.locallyTrivial⟩

def e45LineClassEquiv (X : Scheme.{u}) : Picard.PoincareBundle.Line.Bundles.LineBundleClass X ≃ AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass X where
  toFun := Quotient.map e45LineBundleToHilbertConstruction (fun _ _ h => h)
  invFun := Quotient.map e33LineBundleToPoincareBundle (fun _ _ h => h)
  left_inv q := by induction q using Quotient.inductionOn; rfl
  right_inv q := by induction q using Quotient.inductionOn; rfl

theorem e45LineClassEquiv_mk {X : Scheme.{u}} (L : Picard.PoincareBundle.Line.Bundles.LineBundle X) :
    e45LineClassEquiv X (Picard.PoincareBundle.Line.Bundles.LineBundleClass.mk L) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (e45LineBundleToHilbertConstruction L) := rfl

theorem e45LineClassEquiv_pullback {X Y : Scheme.{u}} (f : X ⟶ Y) (q : Picard.PoincareBundle.Line.Bundles.LineBundleClass Y) :
    e45LineClassEquiv X (Picard.PoincareBundle.Line.Bundles.LineBundleClass.pullback f q) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f (e45LineClassEquiv Y q) := by
  induction q using Quotient.inductionOn
  rfl

def e45LineClassFunctorIso : Picard.PoincareBundle.Line.Bundles.lineBundleClassFunctor ≅ AbelianModuli.HilbertConstruction.Line.Bundles.lineBundleClassFunctor :=
  NatIso.ofComponents (fun X => (e45LineClassEquiv X.unop).toIso) (by
    intro X Y f
    apply ConcreteCategory.ext_apply
    intro q
    exact e45LineClassEquiv_pullback f.unop q)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LineClassComparison.Construction
