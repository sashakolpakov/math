import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.CoordinatePullback
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.PullbackProjection
import OAI.NumberTheory.PadicHodge.GeometricComparison.OpenSectionPullback

/-! # Coordinate Projection -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.CoordinateProjection.IntrinsicCechCoordinatePullback

noncomputable section

/-! The coordinate Čech geometric map is the actual pullback of forms on each refined intersection. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

variable (R : Type) [CommRing R]
  {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)
  {ι κ : Type} (U : ι → Y.left.Opens) (V : κ → X.left.Opens)
  (r : κ → ι) (hr : ∀ i, V i ≤ f.left ⁻¹ᵁ U (r i))

theorem coordinateMap_f_f_π (q n : ℕ) (t : Fin (n + 1) → κ) :
    ((CoordinatePullback.IntrinsicCechCoordinatePullback.coordinateMap R f U V r hr).f q).f n ≫
        Pi.π (fun t : Fin (n + 1) → κ =>
          (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X q).obj (op (∏ᶜ (V ∘ t)))) t =
      Pi.π (fun s : Fin (n + 1) → ι =>
        (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R Y q).obj (op (∏ᶜ (U ∘ s)))) (r ∘ t) ≫
        OpenSectionPullback.DeRham.formsPullbackLE f (∏ᶜ (U ∘ (r ∘ t))) (∏ᶜ (V ∘ t))
          (Cech.PullbackProjection.CechPullback.intersectionHom f.left U V r hr n t).le q := by
  have h := Cech.PullbackProjection.CechPullback.map_f_π R f.left U V r hr (DeRham.Int.formsPullback f q) n t
  have hcomp := OpenSectionPullback.DeRham.formsPullbackLE_eq f (∏ᶜ (U ∘ (r ∘ t))) (∏ᶜ (V ∘ t))
    (Cech.PullbackProjection.CechPullback.intersectionHom f.left U V r hr n t).le q
  exact h.trans (congrArg (fun k =>
    Pi.π (fun s : Fin (n + 1) → ι => (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R Y q).obj (op (∏ᶜ (U ∘ s))))
      (r ∘ t) ≫ k) hcomp.symm)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.CoordinateProjection.IntrinsicCechCoordinatePullback
