import OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.CechScalarGeometricNaturality
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Mapped.ComplexHomologyNaturality
import OAI.AlgebraicGeometry.Crystalline.Cohomology.SectionHypercohomologyInv
import OAI.NumberTheory.PadicHodge.GeometricComparison.ExactHomology

/-! # Intrinsic Cech Scalar Total -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechScalarTotal.BaseIntrinsicCechScalarTotal

noncomputable section

/-! The canonical scalar map on finite Čech totals and cohomology commutes with every compatible geometric refinement. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u₀
section Maps
variable (R S : Type u₀) [CommRing R] [CommRing S] [Algebra R S]
  (X : Over (Spec (CommRingCat.of R))) (Y : Over (Spec (CommRingCat.of S)))
  (f : Y.left ⟶ X.left)
  (hf : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))
  {ι : Type u₀} [Finite ι] (U : ι → X.left.Opens)

abbrev total := (Cech.Descent.CechDescent.bicomplex R X U).total (.up ℕ)

def scalarMap :
    ((NumberTheory.PadicHodge.GeometricComparison.FlatScalar.FlatScalarExtension.moduleFunctor R S).mapHomologicalComplex (.up ℕ)).obj (BaseIntrinsicCechScalarTotal.total R X U) ⟶
      BaseIntrinsicCechScalarTotal.total S Y (fun i => f ⁻¹ᵁ U i) :=
  (Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso (NumberTheory.PadicHodge.GeometricComparison.FlatScalar.FlatScalarExtension.moduleFunctor R S)
    (Cech.Descent.CechDescent.bicomplex R X U)).inv ≫
      HomologicalComplex₂.total.map (IntrinsicCechScalarProjection.BaseIntrinsicCechScalarProjection.map R S X Y f hf U) (.up ℕ)

variable [Module.Flat R S]

def homologyMap (n : ℕ) :
    (NumberTheory.PadicHodge.GeometricComparison.FlatScalar.FlatScalarExtension.moduleFunctor R S).obj ((BaseIntrinsicCechScalarTotal.total R X U).homology n) ⟶
      (BaseIntrinsicCechScalarTotal.total S Y (fun i => f ⁻¹ᵁ U i)).homology n :=
  (Mapped.ComplexHomology.MappedComplexHomology.iso (NumberTheory.PadicHodge.GeometricComparison.FlatScalar.FlatScalarExtension.moduleFunctor R S) (BaseIntrinsicCechScalarTotal.total R X U) n).inv ≫
    HomologicalComplex.homologyMap (scalarMap R S X Y f hf U) n
end Maps

variable (R S : Type u₀) [CommRing R] [CommRing S] [Algebra R S]
  {X₁ X₂ : Over (Spec (CommRingCat.of R))} {Y₁ Y₂ : Over (Spec (CommRingCat.of S))}
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (h₁ : f₁ ≫ X₁.hom = Y₁.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))
  (h₂ : f₂ ≫ X₂.hom = Y₂.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))
  (hsquare : f₁ ≫ u.left = v.left ≫ f₂)
  {ι κ : Type u₀} [Finite ι] [Finite κ] (U : ι → X₂.left.Opens) (V : κ → X₁.left.Opens)
  (r : κ → ι) (hr : ∀ i, V i ≤ u.left ⁻¹ᵁ U (r i))
  (hv : ∀ i, f₁ ⁻¹ᵁ V i ≤ v.left ⁻¹ᵁ (f₂ ⁻¹ᵁ U (r i)))

include hsquare in
theorem naturality :
    ((NumberTheory.PadicHodge.GeometricComparison.FlatScalar.FlatScalarExtension.moduleFunctor R S).mapHomologicalComplex (.up ℕ)).map
      (HomologicalComplex₂.total.map (IntrinsicCechCoordinatePullback.BaseIntrinsicCechCoordinatePullback.coordinateMap R u U V r hr) (.up ℕ)) ≫
        scalarMap R S X₁ Y₁ f₁ h₁ V =
    scalarMap R S X₂ Y₂ f₂ h₂ U ≫
      HomologicalComplex₂.total.map
        (IntrinsicCechCoordinatePullback.BaseIntrinsicCechCoordinatePullback.coordinateMap S v (fun i => f₂ ⁻¹ᵁ U i) (fun i => f₁ ⁻¹ᵁ V i) r hv) (.up ℕ) := by
  let F := NumberTheory.PadicHodge.GeometricComparison.FlatScalar.FlatScalarExtension.moduleFunctor R S
  let a := IntrinsicCechCoordinatePullback.BaseIntrinsicCechCoordinatePullback.coordinateMap R u U V r hr
  let b := IntrinsicCechCoordinatePullback.BaseIntrinsicCechCoordinatePullback.coordinateMap S v
    (fun i => f₂ ⁻¹ᵁ U i) (fun i => f₁ ⁻¹ᵁ V i) r hv
  let T := HomologicalComplex₂.totalFunctor (ModuleCat.{u₀} S) (.up ℕ) (.up ℕ) (.up ℕ)
  have hA := SectionHypercohomologyInv.SectionHypercohomology.inverse_square
    (Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso F (Cech.Descent.CechDescent.bicomplex R X₂ U))
    (Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso F (Cech.Descent.CechDescent.bicomplex R X₁ V)) _ _
    (NumberTheory.PadicHodge.GeometricComparison.Finite.TotalIso.FiniteTotalNaturality.naturality F a)
  have hB := (T.map_comp (NumberTheory.PadicHodge.GeometricComparison.Finite.TotalIso.FiniteTotalNaturality.map F a)
    (IntrinsicCechScalarProjection.BaseIntrinsicCechScalarProjection.map R S X₁ Y₁ f₁ h₁ V)).symm.trans
    ((congrArg T.map (CechScalarGeometricNaturality.BaseIntrinsicCechScalarGeometricNaturality.naturality R S u v f₁ f₂ h₁ h₂ hsquare U V r hr hv)).trans
      (T.map_comp (IntrinsicCechScalarProjection.BaseIntrinsicCechScalarProjection.map R S X₂ Y₂ f₂ h₂ U) b))
  exact NumberTheory.PadicHodge.GeometricComparison.ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _ hA hB

variable [Module.Flat R S]
include hsquare in
theorem homology_naturality (n : ℕ) :
    (NumberTheory.PadicHodge.GeometricComparison.FlatScalar.FlatScalarExtension.moduleFunctor R S).map
      (HomologicalComplex.homologyMap
        (HomologicalComplex₂.total.map (IntrinsicCechCoordinatePullback.BaseIntrinsicCechCoordinatePullback.coordinateMap R u U V r hr) (.up ℕ)) n) ≫
        BaseIntrinsicCechScalarTotal.homologyMap R S X₁ Y₁ f₁ h₁ V n =
    BaseIntrinsicCechScalarTotal.homologyMap R S X₂ Y₂ f₂ h₂ U n ≫ HomologicalComplex.homologyMap
      (HomologicalComplex₂.total.map
        (IntrinsicCechCoordinatePullback.BaseIntrinsicCechCoordinatePullback.coordinateMap S v (fun i => f₂ ⁻¹ᵁ U i) (fun i => f₁ ⁻¹ᵁ V i) r hv) (.up ℕ)) n := by
  let F := NumberTheory.PadicHodge.GeometricComparison.FlatScalar.FlatScalarExtension.moduleFunctor R S
  let a := HomologicalComplex₂.total.map (IntrinsicCechCoordinatePullback.BaseIntrinsicCechCoordinatePullback.coordinateMap R u U V r hr) (.up ℕ)
  have hA := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u₀} R) (.up ℕ) n).map a) F
  have hB := congrArg (HomologicalComplex.homologyFunctor (ModuleCat.{u₀} S) (.up ℕ) n).map
    (naturality R S u v f₁ f₂ h₁ h₂ hsquare U V r hr hv)
  simp only [Functor.map_comp] at hB
  exact NumberTheory.PadicHodge.GeometricComparison.ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _ hA hB

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechScalarTotal.BaseIntrinsicCechScalarTotal
