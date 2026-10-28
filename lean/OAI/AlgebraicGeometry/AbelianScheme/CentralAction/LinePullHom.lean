import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.PullHomNormalization
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.LineEndRigidity
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

/-! # Line Pull Hom -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.LinePullHom.Construction

noncomputable section

/-! Actual line-bundle pullbacks retain all composition comparisons.
Scalar injectivity cancels those pullbacks on isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

universe u

def schemeModulePullbacks : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat :=
  Scheme.Modules.pseudofunctor.comp Bicategory.Adj.forget₁

def overSchemeModulePullbacks (S : Scheme.{u}) :
    Pseudofunctor (LocallyDiscrete (Over S)ᵒᵖ) Cat :=
  (Over.forget S).op.toPseudofunctor.comp schemeModulePullbacks

theorem linePullHom_ext {S : Scheme.{u}} {X T W : Over S}
    (f : T ⟶ X) (g : W ⟶ T) (f' : W ⟶ X) (hf : g ≫ f = f')
    (hg : Function.Injective g.left.appTop) (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left)
    (a b : (L.pullback f.left).sheaf ⟶ (M.pullback f.left).sheaf) [IsIso a]
    (h : pullHom (F := overSchemeModulePullbacks S) a g f' f' hf hf =
      pullHom (F := overSchemeModulePullbacks S) b g f' f' hf hf) : a = b := by
  apply LineEndRigidity.Construction.lineBundle_hom_ext_of_pullback g.left hg (L.pullback f.left) (M.pullback f.left) a b
  exact PullHomNormalization.Construction.map_eq_of_pullHom_eq (overSchemeModulePullbacks S) a b g f' f' hf hf h

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.LinePullHom.Construction
