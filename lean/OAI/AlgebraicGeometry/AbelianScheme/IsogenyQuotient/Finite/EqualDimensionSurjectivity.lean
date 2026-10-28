import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.IntegralDimension

/-! # Equal Dimension Surjectivity -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.EqualDimensionSurjectivity.Construction

noncomputable section

/-! A finite morphism between integral schemes of the same finite
dimension is surjective. Height preservation forces the image of the
generic point to be generic, and the finite image is closed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem finite_same_dimension_surjective {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsFinite f] (hdim : topologicalKrullDim X = topologicalKrullDim Y)
    (hfin : topologicalKrullDim X < ⊤) : Surjective f := by
  have hh : Order.height (f (⊤ : X)) = Order.height (⊤ : Y) := by
    apply WithBot.coe_injective
    rw [← ArithmeticGeometry.OrdinaryLocus.Openness.IntegralDimension.Construction.height_eq_of_isIntegral f, Order.height_top_eq_krullDim, Order.height_top_eq_krullDim]
    exact (ArithmeticGeometry.OrdinaryLocus.Openness.GroupDimension.Construction.topologicalKrullDim_eq_specialization_krullDim X).symm.trans
      (hdim.trans (ArithmeticGeometry.OrdinaryLocus.Openness.GroupDimension.Construction.topologicalKrullDim_eq_specialization_krullDim Y))
  have hheight : Order.height (f (⊤ : X)) < ⊤ := by
    rw [← ArithmeticGeometry.OrdinaryLocus.Openness.IntegralDimension.Construction.height_eq_of_isIntegral f]
    apply WithBot.coe_lt_coe.mp
    rw [Order.height_top_eq_krullDim, ← ArithmeticGeometry.OrdinaryLocus.Openness.GroupDimension.Construction.topologicalKrullDim_eq_specialization_krullDim]
    exact hfin
  have htop : f (⊤ : X) = ⊤ := by
    by_contra h
    have hlt : f (⊤ : X) < (⊤ : Y) := by
      refine lt_iff_le_not_ge.mpr ⟨le_top, ?_⟩
      intro hge
      exact h ((Scheme.le_iff_specializes.mp hge).antisymm (genericPoint_specializes (f ⊤))).eq
    exact (ne_of_lt (Order.height_strictMono hlt hheight)) hh
  have hclosed : IsClosed (Set.range f) := f.isClosedMap.isClosed_range
  refine ⟨fun y => ?_⟩
  exact (genericPoint_specializes y).mem_closed hclosed ⟨⊤, htop⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.EqualDimensionSurjectivity.Construction
