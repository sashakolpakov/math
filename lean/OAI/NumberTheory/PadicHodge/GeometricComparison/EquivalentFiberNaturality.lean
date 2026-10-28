import OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.ScalarCohomologyNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.ScalarFormsChange
import OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.Functor

/-! # Equivalent Fiber Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.EquivalentFiberNaturality.SectionScalarChange

noncomputable section

/-! Natural de Rham comparison for the same geometric fiber over equivalent coefficient fields. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem inverse_transport_square {SX SY RX RY M N : Type*}
    (eX : SX ≃ RX) (eY : SY ≃ RY) (iX : M → RX) (iY : N → RY)
    (p : N → M) (q : SY → SX) (r : RY → RX)
    (hi : ∀ x, iX (p x) = r (iY x)) (he : ∀ x, eX (q x) = r (eY x)) (x : N) :
    eX.symm (iX (p x)) = q (eY.symm (iY x)) := by
  apply eX.injective
  rw [eX.apply_symm_apply, he, eY.apply_symm_apply]
  exact hi x

theorem isoPullback_functor_naturality {C : Type*} [Category* C]
    {T : Type} [CommRing T] {F G : C ⥤ Over (Spec (CommRingCat.of T))}
    (e : F ≅ G) {X Y : C} (f : X ⟶ Y) (n : ℕ) :
    (DeRham.IsoCohomology.isoPullback (e.app X).hom n).toLinearMap.comp (DeRham.Int.pullback (G.map f) n) =
      (DeRham.Int.pullback (F.map f) n).comp (DeRham.IsoCohomology.isoPullback (e.app Y).hom n).toLinearMap := by
  rw [DeRham.IsoCohomology.isoPullback_toLinearMap, DeRham.IsoCohomology.isoPullback_toLinearMap]
  exact (DeRham.Functor.pullback_square (F.map f) (G.map f) (e.hom.app X) (e.hom.app Y)
    (e.hom.naturality f) n).symm

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal

variable {B R S : Type} [CommRing B] [Field R] [Field S]
  (σ : R ≃+* S) (r : B →+* R) (s : B →+* S) (hs : s = σ.toRingHom.comp r)

def fiberCohomologyEquiv (X : Over (Spec (CommRingCat.of B))) (n : ℕ) :
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology R ((Over.pullback (Spec.map (CommRingCat.ofHom r))).obj X) n ≃ₛₗ[σ.toRingHom]
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology S ((Over.pullback (Spec.map (CommRingCat.ofHom s))).obj X) n :=
  (DeRham.IsoCohomology.isoPullback (ScalarFormsChange.SectionScalarChange.restrictedFiberIso σ r s hs X).hom n).trans
    (DeRham.ScalarChange.SectionScalarChange.cohomologyEquiv σ ((Over.pullback (Spec.map (CommRingCat.ofHom s))).obj X) n).symm

theorem fiberCohomologyEquiv_naturality {X Y : Over (Spec (CommRingCat.of B))}
    (f : X ⟶ Y) (n : ℕ)
    (a : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology R ((Over.pullback (Spec.map (CommRingCat.ofHom r))).obj Y) n) :
    fiberCohomologyEquiv σ r s hs X n
        (DeRham.Int.pullback ((Over.pullback (Spec.map (CommRingCat.ofHom r))).map f) n a) =
      DeRham.Int.pullback ((Over.pullback (Spec.map (CommRingCat.ofHom s))).map f) n
        (fiberCohomologyEquiv σ r s hs Y n a) := by
  let FS := Over.pullback (Spec.map (CommRingCat.ofHom s))
  let FR := Over.pullback (Spec.map (CommRingCat.ofHom r))
  let eX := DeRham.ScalarChange.SectionScalarChange.cohomologyEquiv σ (FS.obj X) n
  let eY := DeRham.ScalarChange.SectionScalarChange.cohomologyEquiv σ (FS.obj Y) n
  let iX := DeRham.IsoCohomology.isoPullback (ScalarFormsChange.SectionScalarChange.restrictedFiberIso σ r s hs X).hom n
  let iY := DeRham.IsoCohomology.isoPullback (ScalarFormsChange.SectionScalarChange.restrictedFiberIso σ r s hs Y).hom n
  have hi := isoPullback_functor_naturality (ScalarFormsChange.SectionScalarChange.restrictPullbackIso σ r s hs) f n
  exact inverse_transport_square eX.toEquiv eY.toEquiv iX iY
    (DeRham.Int.pullback (FR.map f) n) (DeRham.Int.pullback (FS.map f) n)
    (DeRham.Int.pullback (DeRham.ScalarImage.SectionScalarChange.restrictMap σ (FS.map f)) n)
    (fun x => LinearMap.congr_fun hi x) (DeRham.ScalarCohomologyNaturality.SectionScalarChange.cohomologyEquiv_naturality σ (FS.map f) n) a

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.EquivalentFiberNaturality.SectionScalarChange
