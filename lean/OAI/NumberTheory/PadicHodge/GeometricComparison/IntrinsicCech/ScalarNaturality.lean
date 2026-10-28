import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.CoordinateProjection
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.ScalarProjection
import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.FormsScalarOpenNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.TotalIso

/-! # Scalar Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.ScalarNaturality.IntrinsicCechScalarGeometricNaturality

noncomputable section

/-! The actual finite Čech scalar map commutes with geometric pullback and the pulled-back cover refinement. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
  {X₁ X₂ : Over (Spec (CommRingCat.of R))}
  {Y₁ Y₂ : Over (Spec (CommRingCat.of S))}
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (h₁ : f₁ ≫ X₁.hom = Y₁.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))
  (h₂ : f₂ ≫ X₂.hom = Y₂.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))
  (hsquare : f₁ ≫ u.left = v.left ≫ f₂)
  {ι κ : Type} [Finite ι] [Finite κ] (U : ι → X₂.left.Opens) (V : κ → X₁.left.Opens)
  (r : κ → ι) (hr : ∀ i, V i ≤ u.left ⁻¹ᵁ U (r i))

include hsquare hr in
omit [Algebra R S] [Finite ι] [Finite κ] in
theorem refinement (i : κ) : f₁ ⁻¹ᵁ V i ≤ v.left ⁻¹ᵁ (f₂ ⁻¹ᵁ U (r i)) :=
  Section.GeometricRestriction.SectionGeometricSquare.preimage_le u.left v.left f₁ f₂ hsquare (U (r i)) (V i) (hr i)

include hsquare in
theorem naturality
    (hv : ∀ i, f₁ ⁻¹ᵁ V i ≤ v.left ⁻¹ᵁ (f₂ ⁻¹ᵁ U (r i))) :
    GeometricComparison.Finite.TotalIso.FiniteTotalNaturality.map (FlatScalar.FlatScalarExtension.moduleFunctor R S)
        (CoordinatePullback.IntrinsicCechCoordinatePullback.coordinateMap R u U V r hr) ≫
        ScalarProjection.IntrinsicCechScalarProjection.map R S X₁ Y₁ f₁ h₁ V =
      ScalarProjection.IntrinsicCechScalarProjection.map R S X₂ Y₂ f₂ h₂ U ≫
        CoordinatePullback.IntrinsicCechCoordinatePullback.coordinateMap S v (fun i => f₂ ⁻¹ᵁ U i) (fun i => f₁ ⁻¹ᵁ V i) r hv := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply HomologicalComplex.Hom.ext
  funext n
  apply Pi.hom_ext
  intro t
  let U₀ := ∏ᶜ (U ∘ (r ∘ t))
  let V₀ := ∏ᶜ (V ∘ t)
  let W₀ := ∏ᶜ (fun i => f₂ ⁻¹ᵁ U ((r ∘ t) i))
  let T₀ := ∏ᶜ (fun i => f₁ ⁻¹ᵁ V (t i))
  let hu₀ : V₀ ≤ u.left ⁻¹ᵁ U₀ := (Cech.PullbackProjection.CechPullback.intersectionHom u.left U V r hr n t).le
  let hv₀ : T₀ ≤ v.left ⁻¹ᵁ W₀ :=
    (Cech.PullbackProjection.CechPullback.intersectionHom v.left (fun i => f₂ ⁻¹ᵁ U i) (fun i => f₁ ⁻¹ᵁ V i) r hv n t).le
  let hT : T₀ ≤ f₁ ⁻¹ᵁ V₀ := (ScalarProjection.IntrinsicCechScalarProjection.intersectionHom R S X₁ Y₁ f₁ V n t).le
  let hW : W₀ ≤ f₂ ⁻¹ᵁ U₀ := (ScalarProjection.IntrinsicCechScalarProjection.intersectionHom R S X₂ Y₂ f₂ U n (r ∘ t)).le
  have hc := Intrinsic.FormsScalarOpenNaturality.IntrinsicFormsScalarOpenMap.geometric_naturality R S u v f₁ f₂ h₁ h₂ hsquare
    U₀ V₀ W₀ T₀ hu₀ hv₀ hT hW q
  exact ScalarProjection.ScalarProjectionSquare.square (FlatScalar.FlatScalarExtension.moduleFunctor R S)
    (((CoordinatePullback.IntrinsicCechCoordinatePullback.coordinateMap R u U V r hr).f q).f n)
    (((CoordinatePullback.IntrinsicCechCoordinatePullback.coordinateMap S v (fun i => f₂ ⁻¹ᵁ U i) (fun i => f₁ ⁻¹ᵁ V i) r hv).f q).f n)
    (((ScalarProjection.IntrinsicCechScalarProjection.map R S X₂ Y₂ f₂ h₂ U).f q).f n)
    (((ScalarProjection.IntrinsicCechScalarProjection.map R S X₁ Y₁ f₁ h₁ V).f q).f n)
    _ _ _ _ _ _ _ _
    (CoordinateProjection.IntrinsicCechCoordinatePullback.coordinateMap_f_f_π R u U V r hr q n t)
    (CoordinateProjection.IntrinsicCechCoordinatePullback.coordinateMap_f_f_π S v (fun i => f₂ ⁻¹ᵁ U i) (fun i => f₁ ⁻¹ᵁ V i) r hv q n t)
    (ScalarProjection.IntrinsicCechScalarProjection.map_f_f_π R S X₂ Y₂ f₂ h₂ U q n (r ∘ t))
    (ScalarProjection.IntrinsicCechScalarProjection.map_f_f_π R S X₁ Y₁ f₁ h₁ V q n t) hc

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.ScalarNaturality.IntrinsicCechScalarGeometricNaturality
