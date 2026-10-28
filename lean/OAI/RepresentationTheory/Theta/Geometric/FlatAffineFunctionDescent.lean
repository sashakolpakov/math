import OAI.RepresentationTheory.Theta.Geometric.FlatEqualizerCoefficients
import OAI.RepresentationTheory.Theta.Geometric.AffineChartSectionCoordinates

/-! # Flat Affine Function Descent -/

namespace OAI.RepresentationTheory.Theta.Geometric.FlatAffineFunctionDescent

noncomputable section

/-! Actual compatible regular functions descend on every flat affine
chart over the parameter equalizer. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

def flatEqualizerSpecMap (A R T : Type) [CommRing A] [CommRing R] [CommRing T]
    [Algebra A R] [Algebra A T] : Spec (.of (T ⊗[A] R)) ⟶ Spec (.of T) :=
  Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : T →ₐ[A] T ⊗[A] R).toRingHom)

variable {A R P T : Type} [CommRing A] [CommRing R] [CommRing P] [CommRing T]
    [Algebra A R] [Algebra A P] [Algebra A T] [Module.Flat A T]

theorem flatEqualizerSpecMap_appTop_injective (hi : Function.Injective (algebraMap A R)) :
    Function.Injective (flatEqualizerSpecMap A R T).appTop :=
  AffineChartSectionCoordinates.specMap_appTop_injective _ (Algebra.TensorProduct.includeLeft_injective hi)

theorem existsUnique_flatEqualizer_function_descent
    (hi : Function.Injective (algebraMap A R)) (f g : R →ₐ[A] P)
    (he : Function.Exact (Algebra.linearMap A R) (f.toLinearMap - g.toLinearMap))
    (r : Γ(Spec (.of (T ⊗[A] R)), ⊤))
    (hr : ∀ {Z : Scheme} (a b : Z ⟶ Spec (.of (T ⊗[A] R))),
      a ≫ flatEqualizerSpecMap A R T = b ≫ flatEqualizerSpecMap A R T → a.appTop r = b.appTop r) :
    ∃! s : Γ(Spec (.of T), ⊤), (flatEqualizerSpecMap A R T).appTop s = r := by
  let a := Algebra.TensorProduct.map (AlgHom.id A T) f
  let b := Algebra.TensorProduct.map (AlgHom.id A T) g
  have hc : a.comp (Algebra.TensorProduct.includeLeft : T →ₐ[A] T ⊗[A] R) =
      b.comp (Algebra.TensorProduct.includeLeft : T →ₐ[A] T ⊗[A] R) := by
    simp only [a, b, Algebra.TensorProduct.map_comp_includeLeft]
  have hp : Spec.map (CommRingCat.ofHom a.toRingHom) ≫ flatEqualizerSpecMap A R T =
      Spec.map (CommRingCat.ofHom b.toRingHom) ≫ flatEqualizerSpecMap A R T :=
    AffineChartSectionCoordinates.specMap_pair_comp_of_ring_eq _ a.toRingHom b.toRingHom (congrArg AlgHom.toRingHom hc)
  have H := hr (Spec.map (CommRingCat.ofHom a.toRingHom)) (Spec.map (CommRingCat.ofHom b.toRingHom)) hp
  have hcoeff : a ((Scheme.ΓSpecIso (.of (T ⊗[A] R))).hom r) =
      b ((Scheme.ΓSpecIso (.of (T ⊗[A] R))).hom r) :=
    (AffineChartSectionCoordinates.specMap_section_naturality a.toRingHom r).symm.trans
      ((congrArg (Scheme.ΓSpecIso (.of (T ⊗[A] P))).hom H).trans
        (AffineChartSectionCoordinates.specMap_section_naturality b.toRingHom r))
  obtain ⟨t, ht⟩ := FlatEqualizerCoefficients.flat_equalizer_coefficient_lift f g he _ hcoeff
  let s := (Scheme.ΓSpecIso (.of T)).inv t
  have hs : (flatEqualizerSpecMap A R T).appTop s = r := by
    apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (T ⊗[A] R))).hom).injective
    unfold flatEqualizerSpecMap
    rw [AffineChartSectionCoordinates.specMap_section_naturality]
    change (Algebra.TensorProduct.includeLeft : T →ₐ[A] T ⊗[A] R)
      ((Scheme.ΓSpecIso (.of T)).hom ((Scheme.ΓSpecIso (.of T)).inv t)) = _
    rw [Iso.inv_hom_id_apply]
    exact ht
  exact ⟨s, hs, fun u hu => flatEqualizerSpecMap_appTop_injective hi (hu.trans hs.symm)⟩

end

end OAI.RepresentationTheory.Theta.Geometric.FlatAffineFunctionDescent
