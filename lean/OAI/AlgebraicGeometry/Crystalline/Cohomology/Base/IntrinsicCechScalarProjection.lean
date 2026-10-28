import OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechScalarBicomplex
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.FormsScalarOpenMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.ScalarProjection

/-! # Intrinsic Cech Scalar Projection -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechScalarProjection.BaseIntrinsicCechScalarProjection

noncomputable section

/-! The native Čech scalar map is given on each intersection by scalar extension and actual restriction of forms. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite Simplicial

universe u

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (X : Over (Spec (CommRingCat.of R))) (Y : Over (Spec (CommRingCat.of S)))
  (f : Y.left ⟶ X.left)
  (h : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))

section General
variable {ι : Type u} [Finite ι] (U : ι → X.left.Opens)

local instance : PreservesFiniteLimits (TopologicalSpace.Opens.map f.base) :=
  IntrinsicCechScalarBicomplex.BaseIntrinsicCechScalarBicomplex.opensFiniteLimits R S X Y f

def map : IntrinsicCechScalarBicomplex.BaseIntrinsicCechScalarBicomplex.source R S X U ⟶
    Cech.Descent.CechDescent.bicomplex S Y (fun i => f ⁻¹ᵁ U i) :=
  (IntrinsicCechScalarBicomplex.BaseIntrinsicCechScalarBicomplex.coefficientIso R S X U).hom ≫
    IntrinsicCechScalarBicomplex.BaseIntrinsicCechScalarBicomplex.map R S X Y f U h ≫
      (IntrinsicCechScalarBicomplex.BaseIntrinsicCechScalarBicomplex.inverseImageIso R S X Y f U).hom

def intersectionHom (n : ℕ) (t : Fin (n + 1) → ι) :
    (∏ᶜ (fun i => f ⁻¹ᵁ U (t i))) ⟶ f ⁻¹ᵁ (∏ᶜ (U ∘ t)) :=
  (PreservesProduct.iso (TopologicalSpace.Opens.map f.base) (U ∘ t)).inv

theorem map_f_f_π (q n : ℕ) (t : Fin (n + 1) → ι) :
    ((BaseIntrinsicCechScalarProjection.map R S X Y f h U).f q).f n ≫
        Pi.π (fun t : Fin (n + 1) → ι =>
          (DeRhamGlobalId.DeRhamGlobal.formsPresheaf S Y q).obj (op (∏ᶜ (fun i => f ⁻¹ᵁ U (t i))))) t =
      (NumberTheory.PadicHodge.GeometricComparison.FlatScalar.FlatScalarExtension.moduleFunctor R S).map
        (Pi.π (fun t : Fin (n + 1) → ι =>
          (DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X q).obj (op (∏ᶜ (U ∘ t)))) t) ≫
        FormsScalarOpenMap.BaseIntrinsicFormsScalarOpenMap.component R S X Y f h (∏ᶜ (U ∘ t))
          (∏ᶜ (fun i => f ⁻¹ᵁ U (t i))) (intersectionHom R S X Y f U n t).le q := by
  let P := DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X q
  let Q := DeRhamGlobalId.DeRhamGlobal.formsPresheaf S Y q
  let F := NumberTheory.PadicHodge.GeometricComparison.FlatScalar.FlatScalarExtension.moduleFunctor R S
  let P₀ := fun t : Fin (n + 1) → ι => P.obj (op (∏ᶜ (U ∘ t)))
  let M₀ := fun t : Fin (n + 1) → ι => Q.obj (op (f ⁻¹ᵁ (∏ᶜ (U ∘ t))))
  let N₀ := fun t : Fin (n + 1) → ι => Q.obj (op (∏ᶜ (fun i => f ⁻¹ᵁ U (t i))))
  let b : ∀ t, F.obj (P₀ t) ⟶ M₀ t := fun t =>
    IntrinsicFormsScalarMap.BaseIntrinsicFormsScalarMap.component R S X Y f h (∏ᶜ (U ∘ t)) q
  let e : ∀ t, M₀ t ≅ N₀ t := fun t =>
    Q.mapIso (PreservesProduct.iso (TopologicalSpace.Opens.map f.base) (U ∘ t)).symm.op
  exact NumberTheory.PadicHodge.GeometricComparison.ScalarProjection.ScalarProjectionSquare.projection F P₀ M₀ N₀ b e t

end General

variable [IsProper X.hom] [Smooth X.hom] [Module.Flat R S]

theorem iso_hom
    (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (algebraMap R S)))) :
    (IntrinsicCechScalarBicomplex.BaseIntrinsicCechScalarBicomplex.iso R S X Y f hp).hom =
      BaseIntrinsicCechScalarProjection.map R S X Y f hp.w (ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts.opens R X) := rfl

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechScalarProjection.BaseIntrinsicCechScalarProjection
