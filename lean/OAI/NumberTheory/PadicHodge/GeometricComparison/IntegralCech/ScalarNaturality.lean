import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralCech.ScalarProjection
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralCech.CoordinatePullback
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.ScalarNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.Functor.SquareCongr
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeCechScalarTotal

/-! # Scalar Naturality -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.GeometricComparison.IntegralCech.ScalarNaturality.IntegralCechScalarGeometricNaturality

/-! The actual first-three Cech scalar map commutes with geometric pullback
and the induced refinement of pulled-back covers. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits ZeroObject _root_.AlgebraicGeometry

variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
  {X₁ X₂ : Over (Spec (CommRingCat.of R))} {Y₁ Y₂ : Over (Spec (CommRingCat.of S))}
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (h₁ : f₁ ≫ X₁.hom = Y₁.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))
  (h₂ : f₂ ≫ X₂.hom = Y₂.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))
  (hsquare : f₁ ≫ u.left = v.left ≫ f₂)
  {ι κ : Type} [Finite ι] [Finite κ] (U : ι → X₂.left.Opens) (V : κ → X₁.left.Opens)
  (r : κ → ι) (hr : ∀ i, V i ≤ u.left ⁻¹ᵁ U (r i))
  (hv : ∀ i, f₁ ⁻¹ᵁ V i ≤ v.left ⁻¹ᵁ (f₂ ⁻¹ᵁ U (r i)))

include hsquare in
theorem naturality :
    GeometricComparison.Finite.TotalIso.FiniteTotalNaturality.map (FlatScalar.FlatScalarExtension.moduleFunctor R S)
        (CoordinatePullback.IntegralCechCoordinatePullback.coordinateMap R u U V r hr) ≫
        ScalarProjection.IntegralCechScalarProjection.map R S X₁ Y₁ f₁ h₁ V =
      ScalarProjection.IntegralCechScalarProjection.map R S X₂ Y₂ f₂ h₂ U ≫
        CoordinatePullback.IntegralCechCoordinatePullback.coordinateMap S v
          (fun i => f₂ ⁻¹ᵁ U i) (fun i => f₁ ⁻¹ᵁ V i) r hv := by
  let F := FlatScalar.FlatScalarExtension.moduleFunctor R S
  have h := IntrinsicCech.ScalarNaturality.IntrinsicCechScalarGeometricNaturality.naturality R S u v f₁ f₂ h₁ h₂ hsquare U V r hr hv
  apply HomologicalComplex.Hom.ext
  funext q
  rcases q with _ | (_ | (_ | q))
  · change (F.mapHomologicalComplex (.up ℕ)).map ((CoordinatePullback.IntegralCechCoordinatePullback.coordinateMap R u U V r hr).f 0) ≫
        (ScalarProjection.IntegralCechScalarProjection.map R S X₁ Y₁ f₁ h₁ V).f 0 =
      (ScalarProjection.IntegralCechScalarProjection.map R S X₂ Y₂ f₂ h₂ U).f 0 ≫
        (CoordinatePullback.IntegralCechCoordinatePullback.coordinateMap S v (fun i => f₂ ⁻¹ᵁ U i) (fun i => f₁ ⁻¹ᵁ V i) r hv).f 0
    exact Functor.SquareCongr.FunctorSquareCongr.square (F.mapHomologicalComplex (.up ℕ)) _ _ _ _ _ _ _ _
      (CoordinatePullback.IntegralCechCoordinatePullback.row_zero R u U V r hr)
      (CoordinatePullback.IntegralCechCoordinatePullback.row_zero S v (fun i => f₂ ⁻¹ᵁ U i) (fun i => f₁ ⁻¹ᵁ V i) r hv)
      (ScalarProjection.IntegralCechScalarProjection.row_zero R S X₂ Y₂ f₂ h₂ U)
      (ScalarProjection.IntegralCechScalarProjection.row_zero R S X₁ Y₁ f₁ h₁ V)
      (congrArg (fun a => a.f 0) h)
  · change (F.mapHomologicalComplex (.up ℕ)).map ((CoordinatePullback.IntegralCechCoordinatePullback.coordinateMap R u U V r hr).f 1) ≫
        (ScalarProjection.IntegralCechScalarProjection.map R S X₁ Y₁ f₁ h₁ V).f 1 =
      (ScalarProjection.IntegralCechScalarProjection.map R S X₂ Y₂ f₂ h₂ U).f 1 ≫
        (CoordinatePullback.IntegralCechCoordinatePullback.coordinateMap S v (fun i => f₂ ⁻¹ᵁ U i) (fun i => f₁ ⁻¹ᵁ V i) r hv).f 1
    exact Functor.SquareCongr.FunctorSquareCongr.square (F.mapHomologicalComplex (.up ℕ)) _ _ _ _ _ _ _ _
      (CoordinatePullback.IntegralCechCoordinatePullback.row_one R u U V r hr)
      (CoordinatePullback.IntegralCechCoordinatePullback.row_one S v (fun i => f₂ ⁻¹ᵁ U i) (fun i => f₁ ⁻¹ᵁ V i) r hv)
      (ScalarProjection.IntegralCechScalarProjection.row_one R S X₂ Y₂ f₂ h₂ U)
      (ScalarProjection.IntegralCechScalarProjection.row_one R S X₁ Y₁ f₁ h₁ V)
      (congrArg (fun a => a.f 1) h)
  · change (F.mapHomologicalComplex (.up ℕ)).map ((CoordinatePullback.IntegralCechCoordinatePullback.coordinateMap R u U V r hr).f 2) ≫
        (ScalarProjection.IntegralCechScalarProjection.map R S X₁ Y₁ f₁ h₁ V).f 2 =
      (ScalarProjection.IntegralCechScalarProjection.map R S X₂ Y₂ f₂ h₂ U).f 2 ≫
        (CoordinatePullback.IntegralCechCoordinatePullback.coordinateMap S v (fun i => f₂ ⁻¹ᵁ U i) (fun i => f₁ ⁻¹ᵁ V i) r hv).f 2
    exact Functor.SquareCongr.FunctorSquareCongr.square (F.mapHomologicalComplex (.up ℕ)) _ _ _ _ _ _ _ _
      (CoordinatePullback.IntegralCechCoordinatePullback.row_two R u U V r hr)
      (CoordinatePullback.IntegralCechCoordinatePullback.row_two S v (fun i => f₂ ⁻¹ᵁ U i) (fun i => f₁ ⁻¹ᵁ V i) r hv)
      (ScalarProjection.IntegralCechScalarProjection.row_two R S X₂ Y₂ f₂ h₂ U)
      (ScalarProjection.IntegralCechScalarProjection.row_two R S X₁ Y₁ f₁ h₁ V)
      (congrArg (fun a => a.f 2) h)
  · let T := AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.cechFunctor S Y₁ (fun i => f₁ ⁻¹ᵁ V i)
    let : T.Additive := by
      change (FormalCoproduct.cochainComplexFunctor
        (FormalCoproduct.mk κ (fun i => f₁ ⁻¹ᵁ V i)).cech).Additive
      infer_instance
    exact (T.map_isZero (isZero_zero (Y₁.left.Opensᵒᵖ ⥤ ModuleCat S))).eq_of_tgt _ _

end NumberTheory.PadicHodge.GeometricComparison.IntegralCech.ScalarNaturality.IntegralCechScalarGeometricNaturality

namespace NumberTheory.PadicHodge.GeometricComparison.IntegralCech.ScalarNaturality.IntegralCechScalarTotalNaturality

/-! The existing integral Cech scalar equivalences on total complexes and
their cohomology commute with actual geometric pullback. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct

variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
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
        (CoordinatePullback.IntegralCechCoordinatePullback.map R u U V r hr) ≫
        (IntegralFirst.ThreeCechScalarTotal.IntegralFirstThreeCechScalarTotal.iso R S X₁ Y₁ f₁ V hp₁ hV).hom =
      (IntegralFirst.ThreeCechScalarTotal.IntegralFirstThreeCechScalarTotal.iso R S X₂ Y₂ f₂ U hp₂ hU).hom ≫
        CoordinatePullback.IntegralCechCoordinatePullback.map S v (fun i => f₂ ⁻¹ᵁ U i) (fun i => f₁ ⁻¹ᵁ V i) r hv := by
  let F := FlatScalar.FlatScalarExtension.moduleFunctor R S
  let T := TotalFinite.IntegerTotalFunctor.functor (ModuleCat.{0} S)
  let b := CoordinatePullback.IntegralCechCoordinatePullback.coordinateMap R u U V r hr
  have h₁ := InverseHom.InverseHomCongr.inverse_square
    (GeometricComparison.Finite.TotalIso.FiniteTotalExtension.iso F (IntegralAffine.CechCoordinateUnit.IntegralAffineCechCoordinateUnit.bicomplex R X₂ U))
    (GeometricComparison.Finite.TotalIso.FiniteTotalExtension.iso F (IntegralAffine.CechCoordinateUnit.IntegralAffineCechCoordinateUnit.bicomplex R X₁ V)) _ _
    (TotalFinite.FiniteTotalExtensionNaturality.naturality F b).symm
  have hs : GeometricComparison.Finite.TotalIso.FiniteTotalNaturality.map F b ≫
        (IntegralFirst.ThreeCechScalarBicomplex.IntegralFirstThreeCechScalarBicomplex.iso R S X₁ Y₁ f₁ V hp₁ hV).hom =
      (IntegralFirst.ThreeCechScalarBicomplex.IntegralFirstThreeCechScalarBicomplex.iso R S X₂ Y₂ f₂ U hp₂ hU).hom ≫
        CoordinatePullback.IntegralCechCoordinatePullback.coordinateMap S v (fun i => f₂ ⁻¹ᵁ U i) (fun i => f₁ ⁻¹ᵁ V i) r hv := by
    rw [ScalarProjection.IntegralCechScalarProjection.iso_hom, ScalarProjection.IntegralCechScalarProjection.iso_hom]
    exact IntegralCechScalarGeometricNaturality.naturality R S u v f₁ f₂ hp₁.w hp₂.w hsquare U V r hr hv
  have h₂ := (T.map_comp _ _).symm.trans ((congrArg T.map hs).trans (T.map_comp _ _))
  exact ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _ h₁ h₂

include hsquare in
theorem cohomology_naturality (n : ℤ)
    (x : S ⊗[R] (IntegralFirst.ThreeCechScalarTotal.IntegralFirstThreeCechScalarTotal.complex R X₂ U).homology n) :
    IntegralFirst.ThreeCechScalarTotal.IntegralFirstThreeCechScalarTotal.cohomologyEquiv R S X₁ Y₁ f₁ V hp₁ hV n
        ((HomologicalComplex.homologyMap (CoordinatePullback.IntegralCechCoordinatePullback.map R u U V r hr) n).hom.baseChange S x) =
      HomologicalComplex.homologyMap
        (CoordinatePullback.IntegralCechCoordinatePullback.map S v (fun i => f₂ ⁻¹ᵁ U i) (fun i => f₁ ⁻¹ᵁ V i) r hv) n
          (IntegralFirst.ThreeCechScalarTotal.IntegralFirstThreeCechScalarTotal.cohomologyEquiv R S X₂ Y₂ f₂ U hp₂ hU n x) := by
  have h := ExactHomology.ExactHomologyComparison.naturality (FlatScalar.FlatScalarExtension.moduleFunctor R S) (.up ℤ)
    (IntegralFirst.ThreeCechScalarTotal.IntegralFirstThreeCechScalarTotal.iso R S X₂ Y₂ f₂ U hp₂ hU)
    (IntegralFirst.ThreeCechScalarTotal.IntegralFirstThreeCechScalarTotal.iso R S X₁ Y₁ f₁ V hp₁ hV)
    (CoordinatePullback.IntegralCechCoordinatePullback.map R u U V r hr)
    (CoordinatePullback.IntegralCechCoordinatePullback.map S v (fun i => f₂ ⁻¹ᵁ U i) (fun i => f₁ ⁻¹ᵁ V i) r hv)
    (naturality R S u v f₁ f₂ hp₁ hp₂ hsquare U V r hr hv hU hV) n
  exact ConcreteCategory.congr_hom h x

end NumberTheory.PadicHodge.GeometricComparison.IntegralCech.ScalarNaturality.IntegralCechScalarTotalNaturality

end

end OAI
