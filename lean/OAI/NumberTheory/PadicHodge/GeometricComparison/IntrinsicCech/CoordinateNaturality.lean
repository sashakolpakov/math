import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.SectionPullbackBicomplex
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.Coordinate
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.Naturality

/-! # Coordinate Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.CoordinateNaturality.IntrinsicCechCoordinateGeometricNaturality

noncomputable section

/-! The actual coordinate Čech–de Rham comparison commutes with geometric pullback and actual cover refinement. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] [Algebra ℚ R]
  {X Y : Over (Spec (CommRingCat.of R))} [IsSeparated X.hom] [IsSeparated Y.hom] (f : X ⟶ Y)
  {ι κ : Type} (U : ι → Y.left.Opens) (V : κ → X.left.Opens)
  (r : κ → ι) (hr : ∀ i, V i ≤ f.left ⁻¹ᵁ U (r i))
  (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ i, IsAffineOpen (V i))

theorem bicomplex_square : CoordinatePullback.IntrinsicCechCoordinatePullback.coordinateMap R f U V r hr ≫
      (Coordinate.IntrinsicCechCoordinateHodge.bicomplexIso R X V hV).hom =
    (Coordinate.IntrinsicCechCoordinateHodge.bicomplexIso R Y U hU).hom ≫
      SectionPullbackBicomplex.IntrinsicCechSectionPullbackBicomplex.map f U V r hr (DeRham.Int.sheafPullback f) := by
  have h₁ := (CoordinatePullback.IntrinsicCechCoordinatePullback.unit_square R f U V r hr).symm
  have h₂ := Section.Hypercohomology.SectionHypercohomology.inverse_square
    (CechBicomplex.IntrinsicCechBicomplex.sectionIso R Y U (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y))
    (CechBicomplex.IntrinsicCechBicomplex.sectionIso R X V (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X)) _ _
    (SectionPullbackBicomplex.IntrinsicCechSectionPullbackBicomplex.deRham_square f U V r hr)
  exact ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _ h₁ h₂

def map : ScalarTotal.IntrinsicCechScalarTotal.complex R Y U ⟶ ScalarTotal.IntrinsicCechScalarTotal.complex R X V :=
  (TotalFinite.IntegerTotalFunctor.functor (ModuleCat.{0} R)).map (CoordinatePullback.IntrinsicCechCoordinatePullback.coordinateMap R f U V r hr)

theorem total_square : IntrinsicCechCoordinateGeometricNaturality.map R f U V r hr ≫ (Coordinate.IntrinsicCechCoordinateHodge.totalIso R X V hV).hom =
    (Coordinate.IntrinsicCechCoordinateHodge.totalIso R Y U hU).hom ≫
      Naturality.IntrinsicCechGeometricNaturality.sectionsMap R f U V r hr := by
  let I := TotalFinite.IntegerTotalFunctor.functor (ModuleCat.{0} R)
  have h₁ : I.map (CoordinatePullback.IntrinsicCechCoordinatePullback.coordinateMap R f U V r hr) ≫
        I.map (Coordinate.IntrinsicCechCoordinateHodge.bicomplexIso R X V hV).hom =
      I.map (Coordinate.IntrinsicCechCoordinateHodge.bicomplexIso R Y U hU).hom ≫
        I.map (SectionPullbackBicomplex.IntrinsicCechSectionPullbackBicomplex.map f U V r hr (DeRham.Int.sheafPullback f)) :=
    (I.map_comp _ _).symm.trans ((congrArg I.map (bicomplex_square R f U V r hr hU hV)).trans (I.map_comp _ _))
  have h₂ := SectionPullbackTotal.IntrinsicCechSectionPullbackTotal.comparison_square f U V r hr (DeRham.Int.sheafPullback f)
  exact ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _ h₁ h₂

variable [Finite ι] [Finite κ] (hcoverU : iSup U = ⊤) (hcoverV : iSup V = ⊤)

theorem naturality (n : ℕ) (x : (ScalarTotal.IntrinsicCechScalarTotal.complex R Y U).homology (n : ℤ)) :
    Coordinate.IntrinsicCechCoordinateHodge.equiv R X V hV hcoverV n
        (HomologicalComplex.homologyMap (IntrinsicCechCoordinateGeometricNaturality.map R f U V r hr) (n : ℤ) x) =
      DeRham.Int.pullback f n (Coordinate.IntrinsicCechCoordinateHodge.equiv R Y U hU hcoverU n x) := by
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{0} R) (.up ℤ) (n : ℤ)
  have hs := (H.map_comp (IntrinsicCechCoordinateGeometricNaturality.map R f U V r hr) (Coordinate.IntrinsicCechCoordinateHodge.totalIso R X V hV).hom).symm.trans
    ((congrArg H.map (total_square R f U V r hr hU hV)).trans
      (H.map_comp (Coordinate.IntrinsicCechCoordinateHodge.totalIso R Y U hU).hom
        (Naturality.IntrinsicCechGeometricNaturality.sectionsMap R f U V r hr)))
  have hx := ConcreteCategory.congr_hom hs x
  exact (congrArg (TruncatedSections.IntrinsicCechHodgeComparison.equiv R X V hV hcoverV n) hx).trans
    (Naturality.IntrinsicCechGeometricNaturality.naturality R f U V r hr hU hcoverU hV hcoverV n
      ((H.mapIso (Coordinate.IntrinsicCechCoordinateHodge.totalIso R Y U hU)).toLinearEquiv x))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.CoordinateNaturality.IntrinsicCechCoordinateGeometricNaturality
