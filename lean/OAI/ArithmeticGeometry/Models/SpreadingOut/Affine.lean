import OAI.ArithmeticGeometry.Models.SpreadingOut.Base
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Affine -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.Affine.Construction

noncomputable section

/-! Affine smooth models and their arithmetic generic-fiber identifications. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct nonZeroDivisors

universe u

abbrev affineOver (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :
    Over (Spec (CommRingCat.of R)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))

instance affineOver_locallyOfFinitePresentation
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] : LocallyOfFinitePresentation (affineOver R A).hom := by
  apply (LocallyOfFinitePresentation.SpecMap_iff _).mpr
  exact RingHom.finitePresentation_algebraMap.mpr inferInstance

/-- The tensor-product description of an affine generic fiber respects its base. -/
def baseChangeAffineIso
    (R K A : Type u) [CommRing R] [CommRing K] [CommRing A]
    [Algebra R K] [Algebra R A] :
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj
        (affineOver R A) ≅ affineOver K (K ⊗[R] A) :=
  Over.isoMk (pullbackSymmetry _ _ ≪≫ pullbackSpecIso R K A) (by
    change (pullbackSymmetry _ _).hom ≫ (pullbackSpecIso R K A).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[R] A))) = _
    rw [pullbackSpecIso_hom_fst, pullbackSymmetry_hom_comp_fst]
    rfl)

def affineOverIso
    {K A B : Type u} [CommRing K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] (e : A ≃ₐ[K] B) :
    affineOver K A ≅ affineOver K B :=
  Over.isoMk (Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.symm.op) (by
    change Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K B)) =
        Spec.map (CommRingCat.ofHom (algebraMap K A))
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact e.symm.commutes x)

/-- Changing an arithmetic base by an isomorphism preserves the generic fiber. -/
def baseChangeAlongIso {S T Z : Scheme.{u}} (X : Over S)
    (e : S ≅ T) (g : Z ⟶ S) :
    (Over.pullback (g ≫ e.hom)).obj ((Over.map e.hom).obj X) ≅
      (Over.pullback g).obj X := by
  have h : IsPullback (pullback.fst X.hom g) (pullback.snd X.hom g)
      (X.hom ≫ e.hom) (g ≫ e.hom) :=
    (IsPullback.of_hasPullback X.hom g).of_iso
      (Iso.refl _) (Iso.refl _) (Iso.refl _) e
      (by simp) (by simp) (by simp) (by simp)
  exact Over.isoMk h.isoPullback.symm h.isoPullback_inv_snd

/-- An arbitrary localization at one element identifies with the corresponding
principal open of the original affine base. -/
def localizationOpenIso
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (d : R) [IsLocalization.Away d S] :
    Spec (CommRingCat.of S) ≅
      (show (Spec (CommRingCat.of R)).Opens from PrimeSpectrum.basicOpen d).toScheme := by
  let U : (Spec (CommRingCat.of R)).Opens := PrimeSpectrum.basicOpen d
  let f := Spec.map (CommRingCat.ofHom (algebraMap R S))
  have : IsOpenImmersion f := IsOpenImmersion.of_isLocalization d
  exact IsOpenImmersion.isoOfRangeEq f U.ι (by
    rw [Scheme.Opens.range_ι]
    exact PrimeSpectrum.localization_away_comap_range S d)

theorem localizationOpenIso_hom_ι
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (d : R) [IsLocalization.Away d S] :
    (localizationOpenIso R S d).hom ≫
      (show (Spec (CommRingCat.of R)).Opens from PrimeSpectrum.basicOpen d).ι =
        Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
    IsOpenImmersion.of_isLocalization d
  let U : (Spec (CommRingCat.of R)).Opens := PrimeSpectrum.basicOpen d
  exact IsOpenImmersion.isoOfRangeEq_hom_fac _ U.ι (by
    rw [Scheme.Opens.range_ι]
    exact PrimeSpectrum.localization_away_comap_range S d)

/-- The affine local step of SpreadingOut, with an actual smooth model over an
arithmetic open and an isomorphism of generic fibers. -/
theorem smooth_affine_scheme_has_arithmetic_model
    (K A : Type u) [Field K] [NumberField K] [CommRing A]
    [Algebra K A] [Algebra.Smooth K A] :
    ∃ (B : Base.Construction.ArithmeticOpen K) (M : Over B.U.toScheme),
      Smooth M.hom ∧
      Nonempty ((Over.pullback B.generic).obj M ≅ affineOver K A) := by
  obtain ⟨d, hd, hpow, A₀, hA₀, hRA₀, hsmooth, ⟨e⟩⟩ :=
    Fg.Construction.smooth_algebra_model_over_localization
      (R := NumberField.RingOfIntegers K) (K := K) A
  let R₀ := Localization.subalgebra.ofField K (Submonoid.powers d) hpow
  let := hA₀
  let := hRA₀
  let := hsmooth
  let B := Base.Construction.arithmeticOpenOfNonzero K d hd
  let j : Spec (CommRingCat.of R₀) ≅ B.U.toScheme :=
    localizationOpenIso (NumberField.RingOfIntegers K) R₀ d
  let g := Spec.map (CommRingCat.ofHom (algebraMap R₀ K))
  let M := (Over.map j.hom).obj (affineOver R₀ A₀)
  have hj : j.hom ≫ B.U.ι =
      Spec.map (CommRingCat.ofHom (algebraMap (NumberField.RingOfIntegers K) R₀)) :=
    localizationOpenIso_hom_ι (NumberField.RingOfIntegers K) R₀ d
  have hg : g ≫ j.hom = B.generic := by
    apply (cancel_mono B.U.ι).mp
    rw [Category.assoc, hj, B.generic_eq]
    change Spec.map (CommRingCat.ofHom (algebraMap R₀ K)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (NumberField.RingOfIntegers K) R₀)) = _
    rw [← Spec.map_comp]
    congr 1
  have hsm : Smooth (affineOver R₀ A₀).hom := by
    apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
    exact RingHom.smooth_algebraMap.mpr inferInstance
  refine ⟨B, M, ?_, ?_⟩
  · change Smooth ((affineOver R₀ A₀).hom ≫ j.hom)
    infer_instance
  · rw [← hg]
    exact ⟨baseChangeAlongIso (affineOver R₀ A₀) j g ≪≫
      baseChangeAffineIso R₀ K A₀ ≪≫ affineOverIso e.symm⟩

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.Affine.Construction
