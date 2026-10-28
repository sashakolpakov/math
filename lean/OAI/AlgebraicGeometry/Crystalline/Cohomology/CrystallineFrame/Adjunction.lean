import OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.Category
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.UniversalProperty
import Mathlib.CategoryTheory.Adjunction.Basic

/-! # Adjunction -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Adjunction.CrystallineFrameAdjunction

noncomputable section

/-!
# The native crystalline frame adjunction

Forgetting lifted polynomial coordinates is left adjoint to the actual
frame extension. The hom-set equivalence is the proved PD evaluation
map, and the counit is the native frame projection.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] (a : σ → B)

def homEquiv (P : FramedCrystalline.Category.FramedCrystallineCategory.Object p k B σ a)
    (Q : Site.Object p k (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B)) :
    (P.base ⟶ Q) ≃ (P ⟶ (FramedCrystalline.Category.FramedCrystallineCategory.frame p k B σ a).obj Q) where
  toFun f :=
    ⟨UniversalMap.CrystallineFrameUniversalMap.map p k B σ a f P.coordinate P.reduction_coordinate,
      UniversalMap.CrystallineFrameUniversalMap.map_coordinate p k B σ a f P.coordinate P.reduction_coordinate⟩
  invFun g := g.hom ≫ (Functor.CrystallineFrameFunctor.projection p k B σ a).app Q
  left_inv f := UniversalMap.CrystallineFrameUniversalMap.map_projection p k B σ a f P.coordinate P.reduction_coordinate
  right_inv g := FramedCrystalline.Category.FramedCrystallineCategory.hom_ext p k B σ a
    (UniversalProperty.CrystallineFrameUniversalProperty.unique p k B σ a
      (g.hom ≫ (Functor.CrystallineFrameFunctor.projection p k B σ a).app Q)
      P.coordinate P.reduction_coordinate g.hom rfl g.coordinate_comm).symm

theorem homEquiv_symm_naturality_right (P : FramedCrystalline.Category.FramedCrystallineCategory.Object p k B σ a)
    {Q Q' : Site.Object p k (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B)}
    (g : P ⟶ (FramedCrystalline.Category.FramedCrystallineCategory.frame p k B σ a).obj Q) (h : Q ⟶ Q') :
    (CrystallineFrameAdjunction.homEquiv p k B σ a P Q').symm (g ≫ (FramedCrystalline.Category.FramedCrystallineCategory.frame p k B σ a).map h) =
      (CrystallineFrameAdjunction.homEquiv p k B σ a P Q).symm g ≫ h := by
  change (g.hom ≫ (Functor.CrystallineFrameFunctor.functor p k B σ a).map h) ≫
    (Functor.CrystallineFrameFunctor.projection p k B σ a).app Q' =
    (g.hom ≫ (Functor.CrystallineFrameFunctor.projection p k B σ a).app Q) ≫ h
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun t => g.hom ≫ t) ((Functor.CrystallineFrameFunctor.projection p k B σ a).naturality h)).trans
      (Category.assoc _ _ _).symm)

def adjunction : FramedCrystalline.Category.FramedCrystallineCategory.forget p k B σ a ⊣ FramedCrystalline.Category.FramedCrystallineCategory.frame p k B σ a :=
  Adjunction.mkOfHomEquiv
    { homEquiv := CrystallineFrameAdjunction.homEquiv p k B σ a
      homEquiv_naturality_left_symm := fun f g => Category.assoc f.hom g.hom _
      homEquiv_naturality_right := by
        intro P Q Q' f g
        apply (CrystallineFrameAdjunction.homEquiv p k B σ a P Q').symm.injective
        exact ((CrystallineFrameAdjunction.homEquiv p k B σ a P Q').symm_apply_apply (f ≫ g)).trans
          ((homEquiv_symm_naturality_right p k B σ a P ((CrystallineFrameAdjunction.homEquiv p k B σ a P Q) f) g).trans
            (congrArg (fun h => h ≫ g) ((CrystallineFrameAdjunction.homEquiv p k B σ a P Q).symm_apply_apply f))).symm }

theorem counit_eq_projection (Q : Site.Object p k (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B)) :
    (adjunction p k B σ a).counit.app Q = (Functor.CrystallineFrameFunctor.projection p k B σ a).app Q := by
  change 𝟙 _ ≫ (Functor.CrystallineFrameFunctor.projection p k B σ a).app Q = _
  exact Category.id_comp _

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Adjunction.CrystallineFrameAdjunction
