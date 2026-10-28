import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LocalizationStalks
import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion

/-! # Localization -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.Localization

noncomputable section

/-! Every point of the spectrum of an actual scheme stalk has the same
local ring and codimension as its image in the scheme. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem stalkMap_isIso (X : Scheme.{u}) (x : X)
    (p : Spec (X.presheaf.stalk x)) : IsIso ((X.fromSpecStalk x).stalkMap p) := by
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top x)
  let A := Γ(X, U)
  let R := X.presheaf.stalk x
  let : Algebra A R := (X.presheaf.germ U x hx).hom.toAlgebra
  let : IsLocalization (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl R :=
    hU.isLocalization_stalk ⟨x, hx⟩
  let : IsIso ((Spec.map (X.presheaf.germ U x hx)).stalkMap p) :=
    LocalizationStalks.localization_stalkMap_isIso A R
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl p
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hx, IsAffineOpen.fromSpecStalk,
    Scheme.Hom.stalkMap_comp]
  infer_instance

theorem coheight_image (X : Scheme.{u}) (x : X)
    (p : Spec (X.presheaf.stalk x)) :
    Order.coheight (X.fromSpecStalk x p) = Order.coheight p := by
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top x)
  let A := Γ(X, U)
  let R := X.presheaf.stalk x
  let : Algebra A R := (X.presheaf.germ U x hx).hom.toAlgebra
  let : IsLocalization (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl R :=
    hU.isLocalization_stalk ⟨x, hx⟩
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hx, IsAffineOpen.fromSpecStalk,
    Scheme.Hom.comp_apply, coheight_eq_of_isOpenImmersion]
  exact LocalizationStalks.localization_coheight A R
    (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl p

theorem height_eq_coheight_image (X : Scheme.{u}) (x : X)
    (p : Spec (X.presheaf.stalk x)) :
    p.asIdeal.height = Order.coheight (X.fromSpecStalk x p) := by
  rw [coheight_image, idealHeight_eq_coheight]

theorem genericPoint_image (X : Scheme.{u}) [IsIntegral X] (x : X) :
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

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.Localization
