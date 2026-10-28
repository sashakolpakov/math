import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.CohomologyProjection
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralCech.CoordinatePullback
import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-! # Naturality -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.GeometricComparison.IntegralCech.Naturality.IntegralCechGeometricNaturality

/-! The existing native integral Cech comparison commutes with the original
geometric pullback on degree-one de Rham cohomology. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] [Module.Flat ℤ R]
  {X Y : Over (Spec (CommRingCat.of R))} [IsSeparated X.hom] [IsSeparated Y.hom] (f : X ⟶ Y)
  {ι κ : Type} [Finite ι] [Finite κ]
  (U : ι → Y.left.Opens) (V : κ → X.left.Opens) (r : κ → ι)
  (hr : ∀ i, V i ≤ f.left ⁻¹ᵁ U (r i))
  (hU : ∀ i, IsAffineOpen (U i)) (hcoverU : iSup U = ⊤)
  (hV : ∀ i, IsAffineOpen (V i)) (hcoverV : iSup V = ⊤)

local notation "KX" => OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.ThreeComplex.FirstThreeComplex.complex (OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X)
local notation "KY" => OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.ThreeComplex.FirstThreeComplex.complex (OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y)

omit [IsSeparated Y.hom] [Finite ι] in
theorem equiv_projection (x : (Integral.DeRhamOneCech.IntegralDeRhamHOneCech.sections R X V).homology 1) :
    Integral.DeRhamOneCech.IntegralDeRhamHOneCech.projectionEquiv R X (Integral.DeRhamOneCech.IntegralDeRhamHOneCech.equiv R X V hV hcoverV x) =
      IntrinsicCech.Terms.IntrinsicCechComparison.equiv R X.left V hcoverV KX
        (IntegralFirst.ThreeCechAcyclic.IntegralFirstThreeCechAcyclic.integerTotal_ext_subsingleton R X V hV) 1 x :=
  (Integral.DeRhamOneCech.IntegralDeRhamHOneCech.projectionEquiv R X).apply_symm_apply _

theorem naturality (x : (Integral.DeRhamOneCech.IntegralDeRhamHOneCech.sections R Y U).homology 1) :
    Integral.DeRhamOneCech.IntegralDeRhamHOneCech.equiv R X V hV hcoverV
      (HomologicalComplex.homologyMap (CoordinatePullback.IntegralCechCoordinatePullback.sectionsMap R f U V r hr) 1 x) =
    DeRham.Int.pullback f 1 (Integral.DeRhamOneCech.IntegralDeRhamHOneCech.equiv R Y U hU hcoverU x) := by
  let s := IntrinsicCech.Resolution.IntrinsicCechResolution.integerEdge R Y.left U KY
  let t := IntrinsicCech.Resolution.IntrinsicCechResolution.integerEdge R X.left V KX
  let a := Integral.CohomologyProjection.IntegralHOneProjectionNaturality.integerMap f
  let b := IntrinsicCech.PullbackTotal.IntrinsicCechPullback.integerMap f U V r hr (IntegralFirst.ThreePullback.IntegralFirstThreePullback.sheafMap f)
  let : QuasiIso s := IntrinsicCech.Resolution.IntrinsicCechResolution.integerEdge_quasiIso R Y.left U KY hcoverU
  let : QuasiIso t := IntrinsicCech.Resolution.IntrinsicCechResolution.integerEdge_quasiIso R X.left V KX hcoverV
  have h := Intrinsic.ResolvedPullback.IntrinsicResolvedPullback.naturality f s t a b
    (IntrinsicCech.PullbackTotal.IntrinsicCechPullback.integerAugmentation f U V r hr (IntegralFirst.ThreePullback.IntegralFirstThreePullback.sheafMap f)) 0 0
    (IntegralFirst.ThreeCechAcyclic.IntegralFirstThreeCechAcyclic.integerTotal_ext_subsingleton R Y U hU)
    (IntegralFirst.ThreeCechAcyclic.IntegralFirstThreeCechAcyclic.integerTotal_ext_subsingleton R X V hV) 1 x
  apply (Integral.DeRhamOneCech.IntegralDeRhamHOneCech.projectionEquiv R X).injective
  erw [equiv_projection R V hV hcoverV]
  have hp := Integral.CohomologyProjection.IntegralHOneProjectionNaturality.naturality f
    (Integral.DeRhamOneCech.IntegralDeRhamHOneCech.equiv R Y U hU hcoverU x)
  change Intrinsic.ResolvedPullback.IntrinsicResolvedPullback.derivedMap f a 1
    (Integral.DeRhamOneCech.IntegralDeRhamHOneCech.projectionEquiv R Y
      (Integral.DeRhamOneCech.IntegralDeRhamHOneCech.equiv R Y U hU hcoverU x)) = _ at hp
  erw [equiv_projection R U hU hcoverU] at hp
  exact h.trans hp

theorem coordinate_naturality (x : (IntegralAffine.CechCoordinateUnit.IntegralAffineCechCoordinateUnit.integerTotal R Y U).homology 1) :
    Integral.GlobalOneBaseChange.IntegralGlobalHOneBaseChange.coordinateEquiv R X V hV hcoverV
      (HomologicalComplex.homologyMap (CoordinatePullback.IntegralCechCoordinatePullback.map R f U V r hr) 1 x) =
    DeRham.Int.pullback f 1 (Integral.GlobalOneBaseChange.IntegralGlobalHOneBaseChange.coordinateEquiv R Y U hU hcoverU x) := by
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{0} R) (.up ℤ) (1 : ℤ)
  have hs := congrArg H.map (CoordinatePullback.IntegralCechCoordinatePullback.total_square R f U V r hr hU hV)
  rw [Functor.map_comp, Functor.map_comp] at hs
  have hx := ConcreteCategory.congr_hom hs x
  exact (congrArg (Integral.DeRhamOneCech.IntegralDeRhamHOneCech.equiv R X V hV hcoverV) hx).trans
    (naturality R f U V r hr hU hcoverU hV hcoverV
      (H.map (Coordinate.IntegralCechCoordinateHodge.totalIso R Y U hU).hom x))

end NumberTheory.PadicHodge.GeometricComparison.IntegralCech.Naturality.IntegralCechGeometricNaturality

namespace NumberTheory.PadicHodge.GeometricComparison.IntegralCech.Naturality.IntegralFirstThreeCechNaturality

/-! The original integral de Rham coordinates in nonnegative
three-term Cech totals preserve actual geometric pullback. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] [Module.Flat ℤ R]

def equiv (Z : Over (Spec (CommRingCat.of R))) [IsSeparated Z.hom]
    {ν : Type} [Finite ν] (W : ν → Z.left.Opens)
    (hW : ∀ i, IsAffineOpen (W i)) (hcW : iSup W = ⊤) :
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology R Z 1 ≃ₗ[R]
      ((IntegralAffine.CechCoordinateUnit.IntegralAffineCechCoordinateUnit.bicomplex R Z W).total (.up ℕ)).homology 1 :=
  (Integral.GlobalOneBaseChange.IntegralGlobalHOneBaseChange.coordinateEquiv R Z W hW hcW).symm.trans
    ((((IntegralAffine.CechCoordinateUnit.IntegralAffineCechCoordinateUnit.bicomplex R Z W).total (.up ℕ)).extendHomologyIso
      ComplexShape.embeddingUpNat (j := 1) rfl).toLinearEquiv)

variable {X Y : Over (Spec (CommRingCat.of R))} [IsSeparated X.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y) {ι κ : Type} [Finite ι] [Finite κ]
  (U : ι → Y.left.Opens) (V : κ → X.left.Opens) (r : κ → ι)
  (hr : ∀ i, V i ≤ f.left ⁻¹ᵁ U (r i))
  (hU : ∀ i, IsAffineOpen (U i)) (hcU : iSup U = ⊤)
  (hV : ∀ i, IsAffineOpen (V i)) (hcV : iSup V = ⊤)

theorem naturality (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology R Y 1) :
    HomologicalComplex.homologyMap
      (HomologicalComplex₂.total.map (CoordinatePullback.IntegralCechCoordinatePullback.coordinateMap R f U V r hr) (.up ℕ)) 1
        (equiv R Y U hU hcU x) = equiv R X V hV hcV (DeRham.Int.pullback f 1 x) := by
  let a := Integral.GlobalOneBaseChange.IntegralGlobalHOneBaseChange.coordinateEquiv R Y U hU hcU
  let b := Integral.GlobalOneBaseChange.IntegralGlobalHOneBaseChange.coordinateEquiv R X V hV hcV
  have h : HomologicalComplex.homologyMap (CoordinatePullback.IntegralCechCoordinatePullback.map R f U V r hr) 1
      (a.symm x) = b.symm (DeRham.Int.pullback f 1 x) := by
    apply b.injective
    exact (IntegralCechGeometricNaturality.coordinate_naturality R f U V r hr hU hcU hV hcV
      (a.symm x)).trans
        ((congrArg (DeRham.Int.pullback f 1) (a.apply_symm_apply x)).trans (b.apply_symm_apply _).symm)
  have he := ConcreteCategory.congr_hom (HomologicalComplex.extendHomologyIso_hom_naturality
    (HomologicalComplex₂.total.map (CoordinatePullback.IntegralCechCoordinatePullback.coordinateMap R f U V r hr) (.up ℕ))
    ComplexShape.embeddingUpNat (j := 1) rfl) (a.symm x)
  exact he.symm.trans (congrArg
    (((IntegralAffine.CechCoordinateUnit.IntegralAffineCechCoordinateUnit.bicomplex R X V).total (.up ℕ)).extendHomologyIso
      ComplexShape.embeddingUpNat (j := 1) rfl).hom h)

end NumberTheory.PadicHodge.GeometricComparison.IntegralCech.Naturality.IntegralFirstThreeCechNaturality

end

end OAI
