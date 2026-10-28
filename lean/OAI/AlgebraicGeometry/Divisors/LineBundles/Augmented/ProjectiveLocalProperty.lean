import OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.ModuleLocalBasis
import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.ProjectivePullback
import OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.ModuleLocalization
import Mathlib.LinearAlgebra.Basis.Prod
import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.DeformationProperties

/-! # Projective Local Property -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.ProjectiveLocalProperty.BundleCycles

noncomputable section

/-! Target-local properties of finite free projective spectra extend
to the actual augmented spectrum of a finite projective module. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {R : Type} [CommRing R] (M : Type) [AddCommGroup M] [Module R M]
    [Module.Projective R M] [Module.Finite R M]
    (P : MorphismProperty Scheme.{0})
    (hP : ∀ (S N κ : Type) [CommRing S] [AddCommGroup N] [Module S N] [Fintype κ] [Nonempty κ],
      Module.Basis κ S N → P (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase S N))

include hP in
theorem augmentedProjective_property_pointChart (q : Spec (.of R)) :
    ∃ (S : CommRingCat.{0}) (i : Spec S ⟶ Spec (.of R)) (Z : Scheme.{0})
      (j : Z ⟶ SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme R (R × M)) (k : Z ⟶ Spec S),
      IsOpenImmersion i ∧ q ∈ Set.range i ∧ IsPullback k j i (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)) ∧ P k := by
  let : q.asIdeal.IsPrime := q.isPrime
  obtain ⟨r, hr, κ, hκ, ⟨b⟩⟩ := LineBundles.Projective.ModuleLocalBasis.BundleCycles.projectiveModule_exists_localBasis M q.asIdeal
  let := hκ
  let := Fintype.ofFinite κ
  let S := Localization.Away r
  let N := LocalizedModule.Away r M
  let f : M →ₗ[R] N := LocalizedModule.mkLinearMap (Submonoid.powers r) M
  let a := ModuleLocalization.BundleCycles.augmentedModuleLocalizationMap (S := S) f
  let i := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let j := SymmetricProjective.Localization.BundleCycles.localizedSymmetricProjectiveMap (S := S) (Submonoid.powers r) a
  let b' : Module.Basis (Unit ⊕ κ) S (S × N) := (Module.Basis.singleton Unit S).prod b
  refine ⟨.of S, i, SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme S (S × N), j, SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase S (S × N),
    IsOpenImmersion.of_isLocalization r, ?_, SymmetricProjective.ProjectivePullback.BundleCycles.symmetricProjective_principal_isPullback (S := S) r a,
    hP S (S × N) (Unit ⊕ κ) b'⟩
  have he : Set.range i = (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) :=
    PrimeSpectrum.localization_away_comap_range S r
  exact (Set.ext_iff.mp he q).mpr hr

include hP in
theorem augmentedProjective_property [IsZariskiLocalAtTarget P] : P (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)) := by
  choose S i Z j k hi hx hs hp using augmentedProjective_property_pointChart (R := R) M P hP
  let C : (Spec (.of R)).OpenCover := Scheme.Cover.mkOfCovers _ (fun q => Spec (S q)) i
    (fun q => ⟨q, hx q⟩) hi
  exact Global.DeformationProperties.BundleCycles.morphismProperty_of_cover_pullbacks P (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)) C Z j k hs hp

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.ProjectiveLocalProperty.BundleCycles
