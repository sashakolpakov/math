import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreePullback
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralCech.Coordinate
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.SectionPullbackBicomplex

/-! # Coordinate Pullback -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralCech.CoordinatePullback.IntegralCechCoordinatePullback

noncomputable section

section

/-! Coordinate and native three-term integral Cech pullbacks agree under the
existing comparison, for actual geometric maps and cover refinements. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (R : Type) [CommRing R]
  {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)
  {ι κ : Type} (U : ι → Y.left.Opens) (V : κ → X.left.Opens)
  (r : κ → ι) (hr : ∀ i, V i ≤ f.left ⁻¹ᵁ U (r i))

local notation "KX" => OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.ThreeComplex.FirstThreeComplex.complex (OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X)
local notation "KY" => OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.ThreeComplex.FirstThreeComplex.complex (OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y)

def coordinateMap : IntegralAffine.CechCoordinateUnit.IntegralAffineCechCoordinateUnit.bicomplex R Y U ⟶
    IntegralAffine.CechCoordinateUnit.IntegralAffineCechCoordinateUnit.bicomplex R X V :=
  Cech.ComplexPullback.CechPullback.bicomplexMap R f.left U V r hr (IntegralFirst.ThreePullback.IntegralFirstThreePullback.presheafMap f)

def sheafMap : IntrinsicCech.CechBicomplex.IntrinsicCechBicomplex.bicomplex R Y U KY ⟶
    IntrinsicCech.CechBicomplex.IntrinsicCechBicomplex.bicomplex R X V KX :=
  Cech.ComplexPullback.CechPullback.bicomplexMap R f.left U V r hr (IntegralFirst.ThreePullback.IntegralFirstThreePullback.underlyingMap f)

theorem unit_square : IntegralAffine.CechCoordinateUnit.IntegralAffineCechCoordinateUnit.map R Y U ≫ sheafMap R f U V r hr =
    coordinateMap R f U V r hr ≫ IntegralAffine.CechCoordinateUnit.IntegralAffineCechCoordinateUnit.map R X V :=
  Cech.ComplexPullback.CechPullback.bicomplex_naturality R f.left U V r hr
    (IntegralFirst.ThreePullback.IntegralFirstThreePullback.presheafMap f) (IntegralFirst.ThreePullback.IntegralFirstThreePullback.underlyingMap f)
    (IntegralFirst.ThreeSheafUnit.IntegralFirstThreeSheafUnit.map R Y) (IntegralFirst.ThreeSheafUnit.IntegralFirstThreeSheafUnit.map R X)
    (IntegralFirst.ThreePullback.IntegralFirstThreePullback.unit_square f).symm

theorem section_square :
    IntrinsicCech.SectionPullbackBicomplex.IntrinsicCechSectionPullbackBicomplex.map f U V r hr (IntegralFirst.ThreePullback.IntegralFirstThreePullback.sheafMap f) ≫
      (IntrinsicCech.CechBicomplex.IntrinsicCechBicomplex.sectionIso R X V KX).hom =
    (IntrinsicCech.CechBicomplex.IntrinsicCechBicomplex.sectionIso R Y U KY).hom ≫ sheafMap R f U V r hr := by
  apply HomologicalComplex.Hom.ext
  funext q
  let P := (KY).X q
  let Q := (KX).X q
  have h := IntrinsicCech.GlobalPullback.IntrinsicCechGlobalPullback.naturality R f U V r hr P Q
    ((IntegralFirst.ThreePullback.IntegralFirstThreePullback.sheafMap f).f q)
  have hc := congrArg (fun a => a.hom) (IntegralFirst.ThreePullback.IntegralFirstThreePullback.sheafMap_adjoint f q)
  exact h.trans (congrArg (fun a => (IntrinsicCech.GlobalSectionFunctor.IntrinsicCechGlobalSectionFunctor.iso R Y U).hom.app P ≫
    Cech.CechPullback.map R f.left U V r hr a) hc)

variable [IsSeparated X.hom] [IsSeparated Y.hom]
  (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ i, IsAffineOpen (V i))

theorem bicomplex_square : coordinateMap R f U V r hr ≫
      (Coordinate.IntegralCechCoordinateHodge.bicomplexIso R X V hV).hom =
    (Coordinate.IntegralCechCoordinateHodge.bicomplexIso R Y U hU).hom ≫
      IntrinsicCech.SectionPullbackBicomplex.IntrinsicCechSectionPullbackBicomplex.map f U V r hr (IntegralFirst.ThreePullback.IntegralFirstThreePullback.sheafMap f) := by
  have h₁ := (unit_square R f U V r hr).symm
  have h₂ := Section.Hypercohomology.SectionHypercohomology.inverse_square
    (IntrinsicCech.CechBicomplex.IntrinsicCechBicomplex.sectionIso R Y U KY)
    (IntrinsicCech.CechBicomplex.IntrinsicCechBicomplex.sectionIso R X V KX) _ _ (section_square R f U V r hr)
  exact ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _ h₁ h₂

def map : IntegralAffine.CechCoordinateUnit.IntegralAffineCechCoordinateUnit.integerTotal R Y U ⟶
    IntegralAffine.CechCoordinateUnit.IntegralAffineCechCoordinateUnit.integerTotal R X V :=
  (TotalFinite.IntegerTotalFunctor.functor (ModuleCat.{0} R)).map (coordinateMap R f U V r hr)

def sectionsMap : IntrinsicCech.Terms.IntrinsicCechComparison.sections R Y.left U KY ⟶
    IntrinsicCech.Terms.IntrinsicCechComparison.sections R X.left V KX :=
  Intrinsic.SectionComplexPullback.IntrinsicSectionComplexPullback.map f
    (IntrinsicCech.PullbackTotal.IntrinsicCechPullback.integerMap f U V r hr (IntegralFirst.ThreePullback.IntegralFirstThreePullback.sheafMap f))

theorem total_square : IntegralCechCoordinatePullback.map R f U V r hr ≫ (Coordinate.IntegralCechCoordinateHodge.totalIso R X V hV).hom =
    (Coordinate.IntegralCechCoordinateHodge.totalIso R Y U hU).hom ≫ sectionsMap R f U V r hr := by
  let T := TotalFinite.IntegerTotalFunctor.functor (ModuleCat.{0} R)
  have h₁ : T.map (coordinateMap R f U V r hr) ≫
        T.map (Coordinate.IntegralCechCoordinateHodge.bicomplexIso R X V hV).hom =
      T.map (Coordinate.IntegralCechCoordinateHodge.bicomplexIso R Y U hU).hom ≫
        T.map (IntrinsicCech.SectionPullbackBicomplex.IntrinsicCechSectionPullbackBicomplex.map f U V r hr (IntegralFirst.ThreePullback.IntegralFirstThreePullback.sheafMap f)) :=
    (T.map_comp _ _).symm.trans ((congrArg T.map (bicomplex_square R f U V r hr hU hV)).trans
      (T.map_comp _ _))
  have h₂ := IntrinsicCech.SectionPullbackTotal.IntrinsicCechSectionPullbackTotal.comparison_square f U V r hr (IntegralFirst.ThreePullback.IntegralFirstThreePullback.sheafMap f)
  rw [Coordinate.IntegralCechCoordinateHodge.totalIso_hom, Coordinate.IntegralCechCoordinateHodge.totalIso_hom]
  exact ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _ h₁ h₂

end

/-! The retained rows of the integral Cech pullback are the original full
geometric pullback rows. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (R : Type) [CommRing R]
  {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)
  {ι κ : Type} (U : ι → Y.left.Opens) (V : κ → X.left.Opens)
  (r : κ → ι) (hr : ∀ i, V i ≤ f.left ⁻¹ᵁ U (r i))

theorem row_zero : (coordinateMap R f U V r hr).f 0 =
    (IntrinsicCech.CoordinatePullback.IntrinsicCechCoordinatePullback.coordinateMap R f U V r hr).f 0 :=
  congrArg (Cech.CechPullback.map R f.left U V r hr)
    (FirstThree.FunctorialMap.FirstThreeFunctorialMap.direct_zero (DeRham.Int.directImagePresheaf f) (DeRham.Int.presheafPullback f))

theorem row_one : (coordinateMap R f U V r hr).f 1 =
    (IntrinsicCech.CoordinatePullback.IntrinsicCechCoordinatePullback.coordinateMap R f U V r hr).f 1 :=
  congrArg (Cech.CechPullback.map R f.left U V r hr)
    (FirstThree.FunctorialMap.FirstThreeFunctorialMap.direct_one (DeRham.Int.directImagePresheaf f) (DeRham.Int.presheafPullback f))

theorem row_two : (coordinateMap R f U V r hr).f 2 =
    (IntrinsicCech.CoordinatePullback.IntrinsicCechCoordinatePullback.coordinateMap R f U V r hr).f 2 :=
  congrArg (Cech.CechPullback.map R f.left U V r hr)
    (FirstThree.FunctorialMap.FirstThreeFunctorialMap.direct_two (DeRham.Int.directImagePresheaf f) (DeRham.Int.presheafPullback f))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralCech.CoordinatePullback.IntegralCechCoordinatePullback
