import OAI.AlgebraicGeometry.Crystalline.Cohomology.RefinedGeometric
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.CoordinateCechUnit
import OAI.AlgebraicGeometry.Crystalline.Cohomology.OpenSectionGeometricPullback

/-! # Intrinsic Cech Coordinate Pullback -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechCoordinatePullback

noncomputable section

/-! The actual native sheaf de Rham pullback is induced by the original presheaf form pullback through the canonical sheafification unit. -/

namespace DeRhamPullback

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)

theorem presheaf_sheaf_pullback_square :
    NumberTheory.PadicHodge.GeometricComparison.SheafificationComplex.SheafificationComplexUnit.unit (Opens.grothendieckTopology Y.left) (DeRhamGlobalId.DeRhamGlobal.presheafComplex R Y) ≫
        ((sheafToPresheaf (Opens.grothendieckTopology Y.left) (ModuleCat.{u} R)).mapHomologicalComplex (.up ℕ)).map
          (DeRhamPullbackTo.DeRhamPullback.sheafDirectImage f) =
      DeRhamPullbackTo.DeRhamPullback.presheafPullback f ≫ ((DeRhamPullbackTo.DeRhamPullback.directImagePresheaf f).mapHomologicalComplex (.up ℕ)).map
        (NumberTheory.PadicHodge.GeometricComparison.SheafificationComplex.SheafificationComplexUnit.unit (Opens.grothendieckTopology X.left) (DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)) := by
  let A := DeRhamPullbackTo.DeRhamPullback.sheafificationComplexAdjunction Y
  have h : A.homEquiv _ _ (DeRhamPullbackTo.DeRhamPullback.sheafDirectImage f) = DeRhamPullbackTo.DeRhamPullback.presheafToDirectImageSheafComplex f :=
    (A.homEquiv _ _).apply_symm_apply _
  exact (A.homEquiv_unit _ _ (DeRhamPullbackTo.DeRhamPullback.sheafDirectImage f)).symm.trans h

end DeRhamPullback

/-! The actual coordinate-form Čech pullback agrees with the actual sheaf direct-image pullback through the native sheafification unit. -/

namespace BaseIntrinsicCechCoordinatePullback
open _root_.CategoryTheory
open _root_.AlgebraicGeometry
section

universe u

variable (R : Type u) [CommRing R]
  {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)
  {ι κ : Type u} (U : ι → Y.left.Opens) (V : κ → X.left.Opens)
  (r : κ → ι) (hr : ∀ i, V i ≤ f.left ⁻¹ᵁ U (r i))

def coordinateMap : Cech.Descent.CechDescent.bicomplex R Y U ⟶ Cech.Descent.CechDescent.bicomplex R X V :=
  RefinedGeometric.RefinedGeometricCechPullback.bicomplexMap R f.left U V r hr (DeRhamPullbackTo.DeRhamPullback.presheafPullback f)

def sheafPresheafMap :
    ((sheafToPresheaf (Opens.grothendieckTopology Y.left) (ModuleCat.{u} R)).mapHomologicalComplex (.up ℕ)).obj
        (DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y) ⟶
      ((RefinedGeometric.RefinedGeometricCechPullback.functor R f.left).mapHomologicalComplex (.up ℕ)).obj
        (((sheafToPresheaf (Opens.grothendieckTopology X.left) (ModuleCat.{u} R)).mapHomologicalComplex (.up ℕ)).obj
          (DeRhamGlobalId.DeRhamGlobal.sheafComplex R X)) :=
  ((sheafToPresheaf (Opens.grothendieckTopology Y.left) (ModuleCat.{u} R)).mapHomologicalComplex (.up ℕ)).map
    (DeRhamPullbackTo.DeRhamPullback.sheafDirectImage f)

def sheafMap : Cech.SectionTotal.CechSectionTotal.directBicomplex R Y U (DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y) ⟶
    Cech.SectionTotal.CechSectionTotal.directBicomplex R X V (DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) :=
  RefinedGeometric.RefinedGeometricCechPullback.bicomplexMap R f.left U V r hr (sheafPresheafMap R f)

theorem unit_square : CoordinateCechUnit.BaseCoordinateCechUnit.map R Y U ≫ sheafMap R f U V r hr =
    coordinateMap R f U V r hr ≫ CoordinateCechUnit.BaseCoordinateCechUnit.map R X V :=
  RefinedGeometric.RefinedGeometricCechPullback.bicomplex_naturality R f.left U V r hr (DeRhamPullbackTo.DeRhamPullback.presheafPullback f)
    (sheafPresheafMap R f)
    (NumberTheory.PadicHodge.GeometricComparison.SheafificationComplex.SheafificationComplexUnit.unit (Opens.grothendieckTopology Y.left) (DeRhamGlobalId.DeRhamGlobal.presheafComplex R Y))
    (NumberTheory.PadicHodge.GeometricComparison.SheafificationComplex.SheafificationComplexUnit.unit (Opens.grothendieckTopology X.left) (DeRhamGlobalId.DeRhamGlobal.presheafComplex R X))
    (DeRhamPullback.presheaf_sheaf_pullback_square f).symm

end

/-! The coordinate Čech geometric map is the actual pullback of forms on each refined intersection. -/

open Limits Opposite

universe v

variable (R : Type v) [CommRing R]
  {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)
  {ι κ : Type v} (U : ι → Y.left.Opens) (V : κ → X.left.Opens)
  (r : κ → ι) (hr : ∀ i, V i ≤ f.left ⁻¹ᵁ U (r i))

theorem coordinateMap_f_f_π (q n : ℕ) (t : Fin (n + 1) → κ) :
    ((coordinateMap R f U V r hr).f q).f n ≫
        Pi.π (fun t : Fin (n + 1) → κ =>
          (DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X q).obj (op (∏ᶜ (V ∘ t)))) t =
      Pi.π (fun s : Fin (n + 1) → ι =>
        (DeRhamGlobalId.DeRhamGlobal.formsPresheaf R Y q).obj (op (∏ᶜ (U ∘ s)))) (r ∘ t) ≫
        OpenSectionGeometricPullback.DeRhamPullback.formsPullbackLE f (∏ᶜ (U ∘ (r ∘ t))) (∏ᶜ (V ∘ t))
          (RefinedGeometric.RefinedGeometricCechPullback.intersectionHom f.left U V r hr n t).le q := by
  have h := RefinedGeometric.RefinedGeometricCechPullback.map_f_π R f.left U V r hr (DeRhamPullbackTo.DeRhamPullback.formsPullback f q) n t
  have hcomp := OpenSectionGeometricPullback.DeRhamPullback.formsPullbackLE_eq f (∏ᶜ (U ∘ (r ∘ t))) (∏ᶜ (V ∘ t))
    (RefinedGeometric.RefinedGeometricCechPullback.intersectionHom f.left U V r hr n t).le q
  exact h.trans (congrArg (fun k =>
    Pi.π (fun s : Fin (n + 1) → ι => (DeRhamGlobalId.DeRhamGlobal.formsPresheaf R Y q).obj (op (∏ᶜ (U ∘ s))))
      (r ∘ t) ≫ k) hcomp.symm)

end BaseIntrinsicCechCoordinatePullback

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechCoordinatePullback
