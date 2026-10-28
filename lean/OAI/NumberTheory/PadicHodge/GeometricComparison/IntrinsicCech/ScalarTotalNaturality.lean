import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.ScalarNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.CoordinateNaturality

/-! # Scalar Total Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.ScalarTotalNaturality.IntrinsicCechScalarTotalNaturality

noncomputable section

/-! The actual scalar equivalences on total Čech complexes and their cohomology commute with geometric pullback. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry
open scoped TensorProduct

variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
  [Algebra ℚ R] [Algebra ℚ S] [Module.Flat R S]
  {X₁ X₂ : Over (Spec (CommRingCat.of R))} [IsSeparated X₁.hom] [IsSeparated X₂.hom]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of S))}
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom (Spec.map (CommRingCat.ofHom (algebraMap R S))))
  (hp₂ : IsPullback f₂ Y₂.hom X₂.hom (Spec.map (CommRingCat.ofHom (algebraMap R S))))
  (hsquare : f₁ ≫ u.left = v.left ≫ f₂)
  {ι κ : Type} [Finite ι] [Finite κ] (U : ι → X₂.left.Opens) (V : κ → X₁.left.Opens)
  (r : κ → ι) (hr : ∀ i, V i ≤ u.left ⁻¹ᵁ U (r i))
  (hv : ∀ i, f₁ ⁻¹ᵁ V i ≤ v.left ⁻¹ᵁ (f₂ ⁻¹ᵁ U (r i)))
  (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ i, IsAffineOpen (V i))

include hsquare in
theorem naturality :
    ((FlatScalar.FlatScalarExtension.moduleFunctor R S).mapHomologicalComplex (.up ℤ)).map
        (CoordinateNaturality.IntrinsicCechCoordinateGeometricNaturality.map R u U V r hr) ≫
        (ScalarTotal.IntrinsicCechScalarTotal.iso R S X₁ Y₁ f₁ V hp₁ hV).hom =
      (ScalarTotal.IntrinsicCechScalarTotal.iso R S X₂ Y₂ f₂ U hp₂ hU).hom ≫
        CoordinateNaturality.IntrinsicCechCoordinateGeometricNaturality.map S v (fun i => f₂ ⁻¹ᵁ U i) (fun i => f₁ ⁻¹ᵁ V i) r hv := by
  let F := FlatScalar.FlatScalarExtension.moduleFunctor R S
  let I := TotalFinite.IntegerTotalFunctor.functor (ModuleCat.{0} S)
  let b := CoordinatePullback.IntrinsicCechCoordinatePullback.coordinateMap R u U V r hr
  have h₁ := InverseHom.InverseHomCongr.inverse_square
    (GeometricComparison.Finite.TotalIso.FiniteTotalExtension.iso F (AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.bicomplex R X₂ U))
    (GeometricComparison.Finite.TotalIso.FiniteTotalExtension.iso F (AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.bicomplex R X₁ V)) _ _
    (TotalFinite.FiniteTotalExtensionNaturality.naturality F b).symm
  have hs := ScalarNaturality.IntrinsicCechScalarGeometricNaturality.naturality R S u v f₁ f₂ hp₁.w hp₂.w hsquare U V r hr hv
  have h₂ := (I.map_comp _ _).symm.trans ((congrArg I.map hs).trans (I.map_comp _ _))
  exact ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _ h₁ h₂

include hsquare in
theorem cohomology_naturality (n : ℤ)
    (x : S ⊗[R] (ScalarTotal.IntrinsicCechScalarTotal.complex R X₂ U).homology n) :
    ScalarTotal.IntrinsicCechScalarTotal.cohomologyEquiv R S X₁ Y₁ f₁ V hp₁ hV n
        ((HomologicalComplex.homologyMap (CoordinateNaturality.IntrinsicCechCoordinateGeometricNaturality.map R u U V r hr) n).hom.baseChange S x) =
      HomologicalComplex.homologyMap
        (CoordinateNaturality.IntrinsicCechCoordinateGeometricNaturality.map S v (fun i => f₂ ⁻¹ᵁ U i) (fun i => f₁ ⁻¹ᵁ V i) r hv) n
          (ScalarTotal.IntrinsicCechScalarTotal.cohomologyEquiv R S X₂ Y₂ f₂ U hp₂ hU n x) := by
  have h := ExactHomology.ExactHomologyComparison.naturality (FlatScalar.FlatScalarExtension.moduleFunctor R S) (.up ℤ)
    (ScalarTotal.IntrinsicCechScalarTotal.iso R S X₂ Y₂ f₂ U hp₂ hU)
    (ScalarTotal.IntrinsicCechScalarTotal.iso R S X₁ Y₁ f₁ V hp₁ hV)
    (CoordinateNaturality.IntrinsicCechCoordinateGeometricNaturality.map R u U V r hr)
    (CoordinateNaturality.IntrinsicCechCoordinateGeometricNaturality.map S v (fun i => f₂ ⁻¹ᵁ U i) (fun i => f₁ ⁻¹ᵁ V i) r hv)
    (naturality R S u v f₁ f₂ hp₁ hp₂ hsquare U V r hr hv hU hV) n
  exact ConcreteCategory.congr_hom h x

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.ScalarTotalNaturality.IntrinsicCechScalarTotalNaturality
