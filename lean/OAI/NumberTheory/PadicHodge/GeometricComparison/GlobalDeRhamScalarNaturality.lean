import OAI.NumberTheory.PadicHodge.GeometricComparison.GlobalDeRhamCoordinate
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.ScalarTotalNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.ScalarEquivTransportNaturality

/-! # Global De Rham Scalar Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.GlobalDeRhamScalarNaturality.GlobalDeRhamScalarExtension

noncomputable section

/-! The original global de Rham scalar equivalence commutes with actual geometric pullback whenever the chosen affine covers have an actual refinement map. -/

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
  (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ i, IsAffineOpen (V i))
  (hcoverU : iSup U = ⊤) (hcoverV : iSup V = ⊤)

include hsquare hr in
theorem naturality (n : ℕ) (x : S ⊗[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology R X₂ n) :
    GlobalDeRhamCoordinate.GlobalDeRhamScalarExtension.equiv R X₁ V hV hcoverV S Y₁ f₁ hp₁ n ((DeRham.Int.pullback u n).baseChange S x) =
      DeRham.Int.pullback v n (GlobalDeRhamCoordinate.GlobalDeRhamScalarExtension.equiv R X₂ U hU hcoverU S Y₂ f₂ hp₂ n x) := by
  let : IsSeparated Y₁.hom := Affine.BaseChangeCover.AffineBaseChangeCover.separated (algebraMap R S) X₁ Y₁ f₁ hp₁
  let : IsSeparated Y₂.hom := Affine.BaseChangeCover.AffineBaseChangeCover.separated (algebraMap R S) X₂ Y₂ f₂ hp₂
  let W := fun i => f₂ ⁻¹ᵁ U i
  let T := fun i => f₁ ⁻¹ᵁ V i
  let hv : ∀ i, T i ≤ v.left ⁻¹ᵁ W (r i) :=
    IntrinsicCech.ScalarNaturality.IntrinsicCechScalarGeometricNaturality.refinement R S u v f₁ f₂ hsquare U V r hr
  let hW : ∀ i, IsAffineOpen (W i) :=
    fun i => Affine.BaseChangeCover.AffineBaseChangeCover.affine (algebraMap R S) X₂ Y₂ f₂ hp₂ (U i) (hU i)
  let hT : ∀ i, IsAffineOpen (T i) :=
    fun i => Affine.BaseChangeCover.AffineBaseChangeCover.affine (algebraMap R S) X₁ Y₁ f₁ hp₁ (V i) (hV i)
  let hcoverW : iSup W = ⊤ := Affine.BaseChangeCover.AffineBaseChangeCover.cover X₂ Y₂ f₂ U hcoverU
  let hcoverT : iSup T = ⊤ := Affine.BaseChangeCover.AffineBaseChangeCover.cover X₁ Y₁ f₁ V hcoverV
  exact ScalarEquivTransportNaturality.FilteredBaseChangeTransport.naturality S
    (GlobalDeRhamCoordinate.GlobalDeRhamScalarExtension.coordinateEquiv R X₁ V hV hcoverV n) (GlobalDeRhamCoordinate.GlobalDeRhamScalarExtension.coordinateEquiv R X₂ U hU hcoverU n)
    (IntrinsicCech.ScalarTotal.IntrinsicCechScalarTotal.cohomologyEquiv R S X₁ Y₁ f₁ V hp₁ hV (n : ℤ))
    (IntrinsicCech.ScalarTotal.IntrinsicCechScalarTotal.cohomologyEquiv R S X₂ Y₂ f₂ U hp₂ hU (n : ℤ))
    (GlobalDeRhamCoordinate.GlobalDeRhamScalarExtension.coordinateEquiv S Y₁ T hT hcoverT n) (GlobalDeRhamCoordinate.GlobalDeRhamScalarExtension.coordinateEquiv S Y₂ W hW hcoverW n)
    (HomologicalComplex.homologyMap (IntrinsicCech.CoordinateNaturality.IntrinsicCechCoordinateGeometricNaturality.map R u U V r hr) (n : ℤ)).hom
    (DeRham.Int.pullback u n)
    (HomologicalComplex.homologyMap (IntrinsicCech.CoordinateNaturality.IntrinsicCechCoordinateGeometricNaturality.map S v W T r hv) (n : ℤ)).hom
    (DeRham.Int.pullback v n)
    (IntrinsicCech.CoordinateNaturality.IntrinsicCechCoordinateGeometricNaturality.naturality R u U V r hr hU hV hcoverU hcoverV n)
    (IntrinsicCech.ScalarTotalNaturality.IntrinsicCechScalarTotalNaturality.cohomology_naturality R S u v f₁ f₂ hp₁ hp₂ hsquare U V r hr hv hU hV (n : ℤ))
    (IntrinsicCech.CoordinateNaturality.IntrinsicCechCoordinateGeometricNaturality.naturality S v W T r hv hW hT hcoverW hcoverT n) x

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.GlobalDeRhamScalarNaturality.GlobalDeRhamScalarExtension
