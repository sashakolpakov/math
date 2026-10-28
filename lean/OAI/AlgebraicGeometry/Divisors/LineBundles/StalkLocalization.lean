import OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizationStalks
import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion

/-! # Stalk Localization -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.StalkLocalization.BundleCycles

noncomputable section

/-!
# LineBundleCycles: local rings and coheights under the actual stalk-spectrum map

Adapted from the localization argument of ProjectionFormula, with default elaboration.
Every point of the spectrum of an actual scheme stalk has the same
local ring and codimension as its image in the scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem affineGerm_stalkMap_isIso (X : Scheme.{u}) (U : X.Opens) (hU : IsAffineOpen U)
    (x : X) (hx : x ∈ U) (p : Spec (X.presheaf.stalk x)) :
    IsIso ((Spec.map (X.presheaf.germ U x hx)).stalkMap p) := by
  let A : Type u := Γ(X, U)
  let R : Type u := X.presheaf.stalk x
  let stalkLocalization_germAlgebra : Algebra A R := (X.presheaf.germ U x hx).hom.toAlgebra
  let stalkLocalization_germLocalization :
      IsLocalization (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl R :=
    hU.isLocalization_stalk ⟨x, hx⟩
  change IsIso ((Spec.map (CommRingCat.ofHom (algebraMap A R))).stalkMap p)
  exact @LocalizationStalks.BundleCycles.localizationStalkMap_isIso A R inferInstance inferInstance stalkLocalization_germAlgebra
    (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl stalkLocalization_germLocalization p

theorem affineGerm_coheight (X : Scheme.{u}) (U : X.Opens) (hU : IsAffineOpen U)
    (x : X) (hx : x ∈ U) (p : Spec (X.presheaf.stalk x)) :
    Order.coheight ((Spec.map (X.presheaf.germ U x hx)) p) = Order.coheight p := by
  let A : Type u := Γ(X, U)
  let R : Type u := X.presheaf.stalk x
  let stalkLocalization_heightAlgebra : Algebra A R := (X.presheaf.germ U x hx).hom.toAlgebra
  let stalkLocalization_heightLocalization :
      IsLocalization (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl R :=
    hU.isLocalization_stalk ⟨x, hx⟩
  change Order.coheight ((Spec.map (CommRingCat.ofHom (algebraMap A R))) p) = Order.coheight p
  exact @LocalizationStalks.BundleCycles.localization_coheight A R inferInstance inferInstance stalkLocalization_heightAlgebra
    (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl stalkLocalization_heightLocalization p

theorem affineOpen_fromSpecStalk_stalkMap_isIso (X : Scheme.{u}) (U : X.Opens) (hU : IsAffineOpen U)
    (x : X) (hx : x ∈ U) (p : Spec (X.presheaf.stalk x)) :
    IsIso ((hU.fromSpecStalk hx).stalkMap p) := by
  let stalkLocalization_germIso := affineGerm_stalkMap_isIso X U hU x hx p
  change IsIso ((Spec.map (X.presheaf.germ U x hx) ≫ hU.fromSpec).stalkMap p)
  rw [Scheme.Hom.stalkMap_comp]
  have hj : IsIso (hU.fromSpec.stalkMap ((Spec.map (X.presheaf.germ U x hx)) p)) := inferInstance
  exact ((@asIso _ _ _ _ _ hj) ≪≫ (@asIso _ _ _ _ _ stalkLocalization_germIso)).isIso_hom

theorem affineOpen_fromSpecStalk_coheight (X : Scheme.{u}) (U : X.Opens) (hU : IsAffineOpen U)
    (x : X) (hx : x ∈ U) (p : Spec (X.presheaf.stalk x)) :
    Order.coheight ((hU.fromSpecStalk hx) p) = Order.coheight p := by
  change Order.coheight (hU.fromSpec ((Spec.map (X.presheaf.germ U x hx)) p)) = Order.coheight p
  exact (coheight_eq_of_isOpenImmersion hU.fromSpec).trans (affineGerm_coheight X U hU x hx p)

theorem fromSpecStalk_stalkMap_isIso (X : Scheme.{u}) (x : X)
    (p : Spec (X.presheaf.stalk x)) : IsIso ((X.fromSpecStalk x).stalkMap p) := by
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top x)
  have he := hU.fromSpecStalk_eq_fromSpecStalk hx
  exact he ▸ affineOpen_fromSpecStalk_stalkMap_isIso X U hU x hx p

theorem fromSpecStalk_coheight (X : Scheme.{u}) (x : X)
    (p : Spec (X.presheaf.stalk x)) :
    Order.coheight (X.fromSpecStalk x p) = Order.coheight p := by
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top x)
  have he := hU.fromSpecStalk_eq_fromSpecStalk hx
  exact he ▸ affineOpen_fromSpecStalk_coheight X U hU x hx p

theorem fromSpecStalk_height_eq_coheight (X : Scheme.{u}) (x : X)
    (p : Spec (X.presheaf.stalk x)) :
    p.asIdeal.height = Order.coheight (X.fromSpecStalk x p) := by
  rw [fromSpecStalk_coheight, idealHeight_eq_coheight]

theorem fromSpecStalk_genericPoint (X : Scheme.{u}) [IsIntegral X] (x : X) :
    X.fromSpecStalk x (genericPoint (Spec (X.presheaf.stalk x))) = genericPoint X := by
  have hmem : genericPoint X ∈ Set.range (X.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]
    exact (genericPoint_spec X).specializes trivial
  obtain ⟨p, hp⟩ := hmem
  apply Inseparable.eq
  apply Specializes.antisymm
  · rw [← hp]
    exact ((genericPoint_spec (Spec (X.presheaf.stalk x))).specializes trivial).map
      (X.fromSpecStalk x).continuous
  · exact (genericPoint_spec X).specializes trivial

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.StalkLocalization.BundleCycles
