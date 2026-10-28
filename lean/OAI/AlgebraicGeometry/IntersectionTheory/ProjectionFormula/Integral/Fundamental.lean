import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ZeroComponents

/-! # Fundamental -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.Fundamental

noncomputable section

/-! On an integral presentation the actual fundamental cycle consists
of its one whole-space support with coefficient one. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.TopologicalSpace

def whole (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier] : IrreducibleCloseds X.carrier :=
  ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X.carrier, isClosed_univ⟩

theorem whole_point (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier] :
    CycleClass.Thom.IntersectionGeometry.supportPoint (whole X) = genericPoint X.carrier :=
  ((whole X).isIrreducible.isGenericPoint_genericPoint (whole X).isClosed).eq (genericPoint_spec X.carrier)

theorem whole_codimension (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier]
    (m : ℕ) [SmoothOfRelativeDimension m X.structureMap] : X.supportCodimension (whole X) = 0 := by
  let C := ZeroComponents.containingComponent X m (whole X)
  have he : C.val = whole X := by
    apply SetLike.coe_injective
    apply Set.Subset.antisymm (Set.subset_univ _)
    exact ZeroComponents.subset_containingComponent X m (whole X)
  rw [← he, C.property]

def support (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier]
    (m : ℕ) [SmoothOfRelativeDimension m X.structureMap] : X.DimensionCycleSupport 0 :=
  ⟨whole X, whole_codimension X m⟩

theorem support_unique (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier]
    (m : ℕ) [SmoothOfRelativeDimension m X.structureMap] (A : X.DimensionCycleSupport 0) :
    A = support X m := by
  apply Subtype.ext
  apply SetLike.coe_injective
  exact (show IsClopen (A.val : Set X.carrier) from
    ⟨A.val.isClosed, Open.Support.codimension_zero_isOpen X m A⟩).eq_univ A.val.isIrreducible.nonempty

theorem fundamental_eq_single (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier]
    (m : ℕ) [SmoothOfRelativeDimension m X.structureMap] :
    ProperCycleLinearity.fundamentalCycle X = Finsupp.single (support X m) 1 := by
  ext A
  rw [ZeroComponents.fundamentalCycle_apply X m, support_unique X m A, Finsupp.single_eq_same]

theorem cycle_eq_single (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier]
    (m : ℕ) [SmoothOfRelativeDimension m X.structureMap] (a : X.RationalDimensionCycle 0) :
    a = Finsupp.single (support X m) (a (support X m)) := by
  ext A
  rw [support_unique X m A, Finsupp.single_eq_same]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.Fundamental
