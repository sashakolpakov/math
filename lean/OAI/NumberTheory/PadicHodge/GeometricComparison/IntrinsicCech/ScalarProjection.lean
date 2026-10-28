import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.ScalarBicomplex
import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.FormsScalarOpenMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.ScalarProjection

/-! # Scalar Projection -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.ScalarProjection.IntrinsicCechScalarProjection

noncomputable section

/-! The native Čech scalar map is given on each intersection by scalar extension and actual restriction of forms. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite Simplicial

variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
  (X : Over (Spec (CommRingCat.of R))) (Y : Over (Spec (CommRingCat.of S)))
  (f : Y.left ⟶ X.left)
  (h : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))
  {ι : Type} [Finite ι] (U : ι → X.left.Opens)

local instance : PreservesFiniteLimits (TopologicalSpace.Opens.map f.base) :=
  ScalarBicomplex.IntrinsicCechScalarBicomplex.opensFiniteLimits R S X Y f

def map : ScalarBicomplex.IntrinsicCechScalarBicomplex.source R S X U ⟶
    AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.bicomplex S Y (fun i => f ⁻¹ᵁ U i) :=
  (ScalarBicomplex.IntrinsicCechScalarBicomplex.coefficientIso R S X U).hom ≫
    ScalarBicomplex.IntrinsicCechScalarBicomplex.map R S X Y f U h ≫
      (ScalarBicomplex.IntrinsicCechScalarBicomplex.inverseImageIso R S X Y f U).hom

def intersectionHom (n : ℕ) (t : Fin (n + 1) → ι) :
    (∏ᶜ (fun i => f ⁻¹ᵁ U (t i))) ⟶ f ⁻¹ᵁ (∏ᶜ (U ∘ t)) :=
  (PreservesProduct.iso (TopologicalSpace.Opens.map f.base) (U ∘ t)).inv

theorem map_f_f_π (q n : ℕ) (t : Fin (n + 1) → ι) :
    ((IntrinsicCechScalarProjection.map R S X Y f h U).f q).f n ≫
        Pi.π (fun t : Fin (n + 1) → ι =>
          (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf S Y q).obj (op (∏ᶜ (fun i => f ⁻¹ᵁ U (t i))))) t =
      (FlatScalar.FlatScalarExtension.moduleFunctor R S).map
        (Pi.π (fun t : Fin (n + 1) → ι =>
          (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X q).obj (op (∏ᶜ (U ∘ t)))) t) ≫
        Intrinsic.FormsScalarOpenMap.IntrinsicFormsScalarOpenMap.component R S X Y f h (∏ᶜ (U ∘ t))
          (∏ᶜ (fun i => f ⁻¹ᵁ U (t i))) (intersectionHom R S X Y f U n t).le q := by
  let P := AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X q
  let Q := AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf S Y q
  let F := FlatScalar.FlatScalarExtension.moduleFunctor R S
  let P₀ := fun t : Fin (n + 1) → ι => P.obj (op (∏ᶜ (U ∘ t)))
  let M₀ := fun t : Fin (n + 1) → ι => Q.obj (op (f ⁻¹ᵁ (∏ᶜ (U ∘ t))))
  let N₀ := fun t : Fin (n + 1) → ι => Q.obj (op (∏ᶜ (fun i => f ⁻¹ᵁ U (t i))))
  let b : ∀ t, F.obj (P₀ t) ⟶ M₀ t := fun t =>
    Intrinsic.FormsScalarMap.IntrinsicFormsScalarMap.component R S X Y f h (∏ᶜ (U ∘ t)) q
  let e : ∀ t, M₀ t ≅ N₀ t := fun t =>
    Q.mapIso (PreservesProduct.iso (TopologicalSpace.Opens.map f.base) (U ∘ t)).symm.op
  exact ScalarProjection.ScalarProjectionSquare.projection F P₀ M₀ N₀ b e t

theorem iso_hom [Algebra ℚ R] [Algebra ℚ S] [Module.Flat R S] [IsSeparated X.hom]
    (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (hU : ∀ i, IsAffineOpen (U i)) :
    (ScalarBicomplex.IntrinsicCechScalarBicomplex.iso R S X Y f U hp hU).hom = IntrinsicCechScalarProjection.map R S X Y f hp.w U := rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.ScalarProjection.IntrinsicCechScalarProjection
