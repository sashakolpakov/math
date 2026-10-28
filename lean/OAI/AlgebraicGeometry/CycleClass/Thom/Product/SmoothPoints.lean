import OAI.AlgebraicGeometry.CycleClass.Thom.Product.PointSections
import OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportTo

/-! # Smooth Points -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Product.SmoothPoints.Constructions

noncomputable section

/-! A complex point of the genuine scheme product is smooth precisely when
both factor points are smooth. Necessity uses the actual product sections
and scalar-compatible local-ring retracts; sufficiency uses smooth open products. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.CycleClass.Thom.Product.PointSections.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SmoothRetract.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportTo.Constructions.SmoothOpen OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportTo.Constructions.PresentationMap

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X Y Z : Over Foundations.Scheme.ProjectiveSpace.complexBase) (πX : Z ⟶ X) (πY : Z ⟶ Y)
  (hprod : IsLimit (BinaryFan.mk πX πY))
  [LocallyOfFinitePresentation X.hom] [LocallyOfFinitePresentation Y.hom]
  [LocallyOfFinitePresentation Z.hom]

include hprod

omit [LocallyOfFinitePresentation Y.hom] in
theorem productPoint_smooth_fst (z : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Z)
    (hz : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying z ∈ Z.hom.smoothLocus) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (z ≫ πX) ∈ X.hom.smoothLocus := by
  let i := PointSections.Constructions.productSectionLeft X Y Z πX πY hprod (z ≫ πY)
  have hs : i.left ≫ πX.left = 𝟙 X.left :=
    congrArg Over.Hom.left (PointSections.Constructions.productSectionLeft_fst X Y Z πX πY hprod (z ≫ πY))
  have hx : i.left (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (z ≫ πX)) = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying z :=
    congrArg (fun p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Z => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying p)
      (PointSections.Constructions.productSectionLeft_point X Y Z πX πY hprod z)
  apply Scheme.SmoothRetract.Constructions.mem_smoothLocus_of_retract i.left πX.left hs X.hom Z.hom i.w πX.w
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (z ≫ πX))
  rw [hx]
  exact hz

omit [LocallyOfFinitePresentation X.hom] in
theorem productPoint_smooth_snd (z : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Z)
    (hz : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying z ∈ Z.hom.smoothLocus) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (z ≫ πY) ∈ Y.hom.smoothLocus := by
  let i := PointSections.Constructions.productSectionRight X Y Z πX πY hprod (z ≫ πX)
  have hs : i.left ≫ πY.left = 𝟙 Y.left :=
    congrArg Over.Hom.left (PointSections.Constructions.productSectionRight_snd X Y Z πX πY hprod (z ≫ πX))
  have hx : i.left (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (z ≫ πY)) = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying z :=
    congrArg (fun p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Z => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying p)
      (PointSections.Constructions.productSectionRight_point X Y Z πX πY hprod z)
  apply Scheme.SmoothRetract.Constructions.mem_smoothLocus_of_retract i.left πY.left hs Y.hom Z.hom i.w πY.w
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (z ≫ πY))
  rw [hx]
  exact hz

theorem productPoint_smooth_of_factors (z : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Z)
    (hx : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (z ≫ πX) ∈ X.hom.smoothLocus)
    (hy : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (z ≫ πY) ∈ Y.hom.smoothLocus) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying z ∈ Z.hom.smoothLocus := by
  let U := Over.mk (Geometric.SmoothStratum.smoothStratumToBase X.hom)
  let V := Over.mk (Geometric.SmoothStratum.smoothStratumToBase Y.hom)
  let i : U ⟶ X := Over.homMk (Geometric.SmoothStratum.smoothStratumι X.hom) rfl
  let j : V ⟶ Y := Over.homMk (Geometric.SmoothStratum.smoothStratumι Y.hom) rfl
  let : Smooth U.hom := inferInstanceAs (Smooth (Geometric.SmoothStratum.smoothStratumToBase X.hom))
  let : Smooth V.hom := inferInstanceAs (Smooth (Geometric.SmoothStratum.smoothStratumToBase Y.hom))
  let : IsOpenImmersion i.left := inferInstanceAs (IsOpenImmersion (Geometric.SmoothStratum.smoothStratumι X.hom))
  let : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion (Geometric.SmoothStratum.smoothStratumι Y.hom))
  apply SupportTo.Constructions.SmoothOpen.productOpen_range_subset_smoothLocus X Y Z πX πY hprod U V i j
  rw [SupportTo.Constructions.PresentationMap.productPresentationMap_range]
  change πX.left (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying z) ∈ Set.range (Geometric.SmoothStratum.smoothStratumι X.hom) ∧
    πY.left (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying z) ∈ Set.range (Geometric.SmoothStratum.smoothStratumι Y.hom)
  rw [Geometric.SmoothStratum.range_smoothStratumι, Geometric.SmoothStratum.range_smoothStratumι]
  exact ⟨hx, hy⟩

theorem productPoint_smooth_iff (z : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Z) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying z ∈ Z.hom.smoothLocus ↔
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (z ≫ πX) ∈ X.hom.smoothLocus ∧
        ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (z ≫ πY) ∈ Y.hom.smoothLocus :=
  ⟨fun hz => ⟨productPoint_smooth_fst X Y Z πX πY hprod z hz,
    productPoint_smooth_snd X Y Z πX πY hprod z hz⟩,
    fun h => productPoint_smooth_of_factors X Y Z πX πY hprod z h.1 h.2⟩

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Product.SmoothPoints.Constructions
