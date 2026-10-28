import OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.Geometry

/-! # Geometric Galois -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.GeometricGalois

noncomputable section

/-!
# Field automorphisms of the actual geometric fiber

Spec is contravariant: multiplying field automorphisms composes the induced
scheme isomorphisms in the reverse functional order. The pullback construction
preserves this law.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.Geometry

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

theorem scalarSchemeIso_one : IntegralComparison.Frobenius.Geometry.scalarSchemeIso (1 : L ≃ₐ[K] L) = Iso.refl _ := by
  apply Iso.ext
  exact Scheme.Spec.map_id _

theorem scalarSchemeIso_mul (σ τ : L ≃ₐ[K] L) :
    IntegralComparison.Frobenius.Geometry.scalarSchemeIso (σ * τ) = IntegralComparison.Frobenius.Geometry.scalarSchemeIso σ ≪≫ IntegralComparison.Frobenius.Geometry.scalarSchemeIso τ := by
  apply Iso.ext
  exact Spec.map_comp (CommRingCat.ofHom τ.toRingHom) (CommRingCat.ofHom σ.toRingHom)

variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K))

theorem geometricFiberIso_one :
    IntegralComparison.Frobenius.Geometry.geometricFiberIso f (1 : L ≃ₐ[K] L) = Iso.refl _ := by
  apply Iso.ext
  apply pullback.hom_ext
  · rw [IntegralComparison.Frobenius.Geometry.geometricFiberIso_hom_fst]
    exact (Category.id_comp _).symm
  · rw [IntegralComparison.Frobenius.Geometry.geometricFiberIso_hom_snd, scalarSchemeIso_one]
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

theorem geometricFiberIso_mul (σ τ : L ≃ₐ[K] L) :
    IntegralComparison.Frobenius.Geometry.geometricFiberIso f (σ * τ) = IntegralComparison.Frobenius.Geometry.geometricFiberIso f σ ≪≫ IntegralComparison.Frobenius.Geometry.geometricFiberIso f τ := by
  apply Iso.ext
  apply pullback.hom_ext
  · change (IntegralComparison.Frobenius.Geometry.geometricFiberIso f (σ * τ)).hom ≫ pullback.fst f _ =
      ((IntegralComparison.Frobenius.Geometry.geometricFiberIso f σ).hom ≫ (IntegralComparison.Frobenius.Geometry.geometricFiberIso f τ).hom) ≫ pullback.fst f _
    rw [Category.assoc, IntegralComparison.Frobenius.Geometry.geometricFiberIso_hom_fst, IntegralComparison.Frobenius.Geometry.geometricFiberIso_hom_fst,
      IntegralComparison.Frobenius.Geometry.geometricFiberIso_hom_fst]
  · change (IntegralComparison.Frobenius.Geometry.geometricFiberIso f (σ * τ)).hom ≫ pullback.snd f _ =
      ((IntegralComparison.Frobenius.Geometry.geometricFiberIso f σ).hom ≫ (IntegralComparison.Frobenius.Geometry.geometricFiberIso f τ).hom) ≫ pullback.snd f _
    rw [IntegralComparison.Frobenius.Geometry.geometricFiberIso_hom_snd f (σ * τ), Category.assoc,
      IntegralComparison.Frobenius.Geometry.geometricFiberIso_hom_snd f τ, ← Category.assoc (IntegralComparison.Frobenius.Geometry.geometricFiberIso f σ).hom,
      IntegralComparison.Frobenius.Geometry.geometricFiberIso_hom_snd f σ, scalarSchemeIso_mul]
    exact (Category.assoc _ _ _).symm

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.GeometricGalois
