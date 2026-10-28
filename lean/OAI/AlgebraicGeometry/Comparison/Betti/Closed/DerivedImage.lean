import OAI.AlgebraicGeometry.Comparison.Betti.Closed.PushforwardExact
import OAI.AlgebraicGeometry.Comparison.Betti.ExactDerivedAdjunction
import OAI.AlgebraicGeometry.Comparison.Betti.Derived.ConstantPullback

/-! # Derived Image -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Closed.DerivedImage

noncomputable section

/-! The actual closed direct image and inverse image form an exact derived adjunction. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

variable {M N : TopCat.{0}} (f : M ⟶ N)
  (hf : Topology.IsInducing f) (hclosed : IsClosed (Set.range f))

def closedDerivedDirectImage : DerivedCategory (ConstantSheafSections.ComplexSheaves M) ⥤ DerivedCategory (ConstantSheafSections.ComplexSheaves N) := by
  have := (PushforwardExact.closedPushforwardExact f hf hclosed).1
  have := (PushforwardExact.closedPushforwardExact f hf hclosed).2
  exact (TopologicalSheafPullback.sheafDirectImage f).mapDerivedCategory

instance closedDerivedDirectImageAdditive : (closedDerivedDirectImage f hf hclosed).Additive := by
  have := (PushforwardExact.closedPushforwardExact f hf hclosed).1
  have := (PushforwardExact.closedPushforwardExact f hf hclosed).2
  exact inferInstanceAs ((TopologicalSheafPullback.sheafDirectImage f).mapDerivedCategory.Additive)

instance closedDerivedDirectImageLinear : (closedDerivedDirectImage f hf hclosed).Linear ℂ := by
  have := (PushforwardExact.closedPushforwardExact f hf hclosed).1
  have := (PushforwardExact.closedPushforwardExact f hf hclosed).2
  exact inferInstanceAs ((TopologicalSheafPullback.sheafDirectImage f).mapDerivedCategory.Linear ℂ)

instance closedDerivedDirectImageCommShift : (closedDerivedDirectImage f hf hclosed).CommShift ℤ := by
  have := (PushforwardExact.closedPushforwardExact f hf hclosed).1
  have := (PushforwardExact.closedPushforwardExact f hf hclosed).2
  exact inferInstanceAs ((TopologicalSheafPullback.sheafDirectImage f).mapDerivedCategory.CommShift ℤ)

def closedDerivedDirectImageFactors :
    DerivedCategory.Q ⋙ closedDerivedDirectImage f hf hclosed ≅
      (TopologicalSheafPullback.sheafDirectImage f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q := by
  have := (PushforwardExact.closedPushforwardExact f hf hclosed).1
  have := (PushforwardExact.closedPushforwardExact f hf hclosed).2
  exact (TopologicalSheafPullback.sheafDirectImage f).mapDerivedCategoryFactors

def closedDerivedImageAdjunction :
    (TopologicalSheafPullback.sheafInverseImage f).mapDerivedCategory ⊣ closedDerivedDirectImage f hf hclosed := by
  have := (PushforwardExact.closedPushforwardExact f hf hclosed).1
  have := (PushforwardExact.closedPushforwardExact f hf hclosed).2
  exact ExactDerivedAdjunction.exactAdjunction (TopologicalSheafPullback.sheafImageAdjunction f)

theorem closedDerivedImageAdjunction_unit (K : CochainComplex (ConstantSheafSections.ComplexSheaves N) ℤ) :
    (closedDerivedImageAdjunction f hf hclosed).unit.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((Complex.Adjunction.onComplexes (TopologicalSheafPullback.sheafImageAdjunction f)
          (ComplexShape.up ℤ)).unit.app K) ≫
        (closedDerivedDirectImageFactors f hf hclosed).inv.app
          (((TopologicalSheafPullback.sheafInverseImage f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        (closedDerivedDirectImage f hf hclosed).map
          ((TopologicalSheafPullback.sheafInverseImage f).mapDerivedCategoryFactors.inv.app K) := by
  have := (PushforwardExact.closedPushforwardExact f hf hclosed).1
  have := (PushforwardExact.closedPushforwardExact f hf hclosed).2
  exact ExactDerivedAdjunction.exactAdjunction_unit (TopologicalSheafPullback.sheafImageAdjunction f) K

def closedDerivedImageHomLinearEquiv (A : DerivedCategory (ConstantSheafSections.ComplexSheaves N))
    (B : DerivedCategory (ConstantSheafSections.ComplexSheaves M)) :
    ((TopologicalSheafPullback.sheafInverseImage f).mapDerivedCategory.obj A ⟶ B) ≃ₗ[ℂ]
      (A ⟶ (closedDerivedDirectImage f hf hclosed).obj B) where
  __ := (closedDerivedImageAdjunction f hf hclosed).homEquiv A B
  map_add' a b := by
    let adj := closedDerivedImageAdjunction f hf hclosed
    change adj.homEquiv A B (a + b) = adj.homEquiv A B a + adj.homEquiv A B b
    simp only [Adjunction.homEquiv_unit, Functor.map_add, Preadditive.comp_add]
  map_smul' c a := by
    let adj := closedDerivedImageAdjunction f hf hclosed
    change adj.homEquiv A B (c • a) = c • adj.homEquiv A B a
    simp only [Adjunction.homEquiv_unit, Functor.map_smul, Linear.comp_smul]

end

end OAI.AlgebraicGeometry.Comparison.Betti.Closed.DerivedImage
