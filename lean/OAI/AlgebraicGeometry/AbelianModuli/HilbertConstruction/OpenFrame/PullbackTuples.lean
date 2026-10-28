import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.TupleRestrictions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PulledBackFrameTransitions

/-! # Pullback Tuples -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.PullbackTuples

noncomputable section

/-! Pullback of actual regular-function frame coordinates along an arbitrary scheme morphism is semilinear over the structural section map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {ι : Type u} (U : ι → Y.Opens) (f : X ⟶ Y)

def openFramePullbackTuple (W : Y.Opens) :
    SectionModules.OpenFrameLocalTuple U W →ₛₗ[(f.app W).hom]
      SectionModules.OpenFrameLocalTuple (fun i => f ⁻¹ᵁ U i) (f ⁻¹ᵁ W) where
  toFun x i := f.app (W ⊓ U i) (x i)
  map_add' x y := by
    funext i
    exact (f.app (W ⊓ U i)).hom.map_add (x i) (y i)
  map_smul' r x := by
    funext i
    change f.app (W ⊓ U i)
      (@Mul.mul Γ(Y, W ⊓ U i) inferInstance
        (Y.presheaf.map (homOfLE (show W ⊓ U i ≤ W from inf_le_left)).op r) (x i)) =
      @Mul.mul Γ(X, f ⁻¹ᵁ W ⊓ f ⁻¹ᵁ U i) inferInstance
        (X.presheaf.map (homOfLE (show f ⁻¹ᵁ W ⊓ f ⁻¹ᵁ U i ≤ f ⁻¹ᵁ W from inf_le_left)).op (f.app W r))
        (f.app (W ⊓ U i) (x i))
    have hn := ConcreteCategory.congr_hom
      (f.naturality (homOfLE (show W ⊓ U i ≤ W from inf_le_left)).op) r
    exact ((f.app (W ⊓ U i)).hom.map_mul _ _).trans
      (congrArg (fun a : Γ(X, f ⁻¹ᵁ (W ⊓ U i)) => a * f.app (W ⊓ U i) (x i)) hn)

theorem openFramePullbackTuple_restrict {V W : Y.Opens} (h : W ≤ V) (x : SectionModules.OpenFrameLocalTuple U V) :
    openFramePullbackTuple U f W (TupleRestrictions.openFrameTupleRestriction U h x) =
      TupleRestrictions.openFrameTupleRestriction (fun i => f ⁻¹ᵁ U i) ((TopologicalSpace.Opens.map f.base).monotone h)
        (openFramePullbackTuple U f V x) := by
  funext i
  exact ConcreteCategory.congr_hom
    (f.naturality (homOfLE (inf_le_inf h (le_refl (U i)))).op) (x i)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.PullbackTuples
