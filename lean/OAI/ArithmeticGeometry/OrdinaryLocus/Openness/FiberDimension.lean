import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FiberDimensionCharts

/-! # Fiber Dimension -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FiberDimension.Construction

noncomputable section

/-! Local constancy of the dimension of the group fibers in Openness. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory MonObj
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {S : Scheme} (A : Over S) [GrpObj A] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]

/-- Fiber dimension is locally constant for the group schemes in Openness. -/
theorem isLocallyConstant_fiberKrullDim :
    IsLocallyConstant (fun s : S => topologicalKrullDim (A.hom.fiber s)) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro s
  let x : A.left := η[A].left s
  have hx : A.hom x = s := by
    change (η[A].left ≫ A.hom) s = s
    simp
  obtain ⟨n, U, V, _, _, hxV, e, hn⟩ := SmoothDimensionCharts.Construction.exists_smoothOfRelativeDimension_chart A.hom x
  let B : Over S := Over.mk (V.ι ≫ A.hom)
  let i : B ⟶ A := Over.homMk V.ι
  have : IsOpenImmersion i.left := inferInstanceAs (IsOpenImmersion V.ι)
  have : Smooth B.hom := inferInstanceAs (Smooth (V.ι ≫ A.hom))
  have : SmoothOfRelativeDimension n B.hom := by
    change SmoothOfRelativeDimension n (V.ι ≫ A.hom)
    rw [← Scheme.Hom.resLE_comp_ι A.hom e]
    have : SmoothOfRelativeDimension n (A.hom.resLE U V e) := hn
    exact inferInstanceAs (SmoothOfRelativeDimension (n + 0) (A.hom.resLE U V e ≫ U.ι))
  have hs : s ∈ Set.range B.hom := ⟨⟨x, hxV⟩, hx⟩
  refine ⟨Set.range B.hom, B.hom.isOpenMap.isOpen_range, hs, ?_⟩
  intro t ht
  exact (FiberDimensionCharts.Construction.dimension_fiber_of_smooth_chart A B i n t ht).trans
    (FiberDimensionCharts.Construction.dimension_fiber_of_smooth_chart A B i n s hs).symm

/-- The natural-number dimension of a fiber, agreeing with the specification. -/
def fiberDimension (s : S) : ℕ := (GeometricDimension.Construction.exists_nat_dimension_fiber_group A s).choose

theorem fiberDimension_spec (s : S) :
    topologicalKrullDim (A.hom.fiber s) = (fiberDimension A s : WithBot ℕ∞) :=
  (GeometricDimension.Construction.exists_nat_dimension_fiber_group A s).choose_spec

/-- The natural-number fiber dimension is locally constant. -/
theorem isLocallyConstant_fiberDimension : IsLocallyConstant (fiberDimension A) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro s
  obtain ⟨U, hU, hs, hconst⟩ := (isLocallyConstant_fiberKrullDim A).exists_open s
  refine ⟨U, hU, hs, fun t ht => ?_⟩
  have h := hconst t ht
  rw [fiberDimension_spec, fiberDimension_spec] at h
  exact_mod_cast h

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FiberDimension.Construction
