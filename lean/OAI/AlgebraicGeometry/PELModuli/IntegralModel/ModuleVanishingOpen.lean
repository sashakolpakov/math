import OAI.AlgebraicGeometry.SheafCohomology.Projective.ModuleZeroCover
import OAI.AlgebraicGeometry.SheafCohomology.Projective.ModuleRestrictLimits
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OpenRestrictionComposition

/-! # Module Vanishing Open -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.ModuleVanishingOpen

noncomputable section

/-! The largest open on which an actual module sheaf vanishes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

theorem module_restrict_isZero_of_le {X : Scheme.{u}} (M : X.Modules)
    {U V : X.Opens} (h : V ≤ U) (hU : IsZero (M.restrict U.ι)) :
    IsZero (M.restrict V.ι) := by
  let e := (restrictFunctorCongr (X.homOfLE_ι h).symm).app M ≪≫
    (restrictFunctorComp (X.homOfLE h) U.ι).app M
  exact e.isZero_iff.mpr ((restrictFunctor (X.homOfLE h)).map_isZero hU)

theorem module_restrict_preimage_isZero {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules)
    (U : Y.Opens) (hU : IsZero (M.restrict U.ι)) :
    IsZero ((M.restrict f).restrict (f ⁻¹ᵁ U).ι) := by
  let e := ((restrictFunctorComp (f ⁻¹ᵁ U).ι f).app M).symm ≪≫
    (restrictFunctorCongr (morphismRestrict_ι f U).symm).app M ≪≫
    (restrictFunctorComp (f ∣_ U) U.ι).app M
  exact e.isZero_iff.mpr ((restrictFunctor (f ∣_ U)).map_isZero hU)

def moduleVanishingOpen {X : Scheme.{u}} (M : X.Modules) : X.Opens :=
  ⨆ (U : X.Opens) (_ : IsZero (M.restrict U.ι)), U

theorem mem_moduleVanishingOpen {X : Scheme.{u}} (M : X.Modules) (x : X) :
    x ∈ moduleVanishingOpen M ↔
      ∃ U : X.Opens, x ∈ U ∧ IsZero (M.restrict U.ι) := by
  simp only [moduleVanishingOpen, Opens.mem_iSup]
  exact ⟨fun ⟨U, h, hx⟩ => ⟨U, hx, h⟩, fun ⟨U, hx, h⟩ => ⟨U, h, hx⟩⟩

theorem moduleVanishingOpen_restrict_isZero {X : Scheme.{u}} (M : X.Modules) :
    IsZero (M.restrict (moduleVanishingOpen M).ι) := by
  let W := moduleVanishingOpen M
  let I := {U : X.Opens // IsZero (M.restrict U.ι)}
  let V : I → W.toScheme.Opens := fun i => W.ι ⁻¹ᵁ i.val
  have hV : ⨆ i, V i = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨U, hx, hU⟩ := (mem_moduleVanishingOpen M x.val).mp x.property
    exact Opens.mem_iSup.mpr ⟨⟨U, hU⟩, hx⟩
  exact SheafCohomology.Projective.ModuleZeroCover.module_isZero_of_restrict_cover V hV (M.restrict W.ι)
    (fun i => module_restrict_preimage_isZero W.ι M i.val i.property)

theorem module_restrict_isZero_iff_le_vanishingOpen {X : Scheme.{u}}
    (M : X.Modules) (U : X.Opens) :
    IsZero (M.restrict U.ι) ↔ U ≤ moduleVanishingOpen M := by
  constructor
  · intro h x hx
    exact (mem_moduleVanishingOpen M x).mpr ⟨U, hx, h⟩
  · intro h
    exact module_restrict_isZero_of_le M h (moduleVanishingOpen_restrict_isZero M)

theorem moduleVanishingOpen_eq_top_iff {X : Scheme.{u}} (M : X.Modules) :
    moduleVanishingOpen M = ⊤ ↔ IsZero M := by
  constructor
  · intro h
    exact SheafCohomology.Projective.ModuleZeroCover.module_isZero_of_restrict_cover (fun _ : Unit => moduleVanishingOpen M)
      (by simpa using h) M (fun _ => moduleVanishingOpen_restrict_isZero M)
  · intro h
    apply top_unique
    exact (module_restrict_isZero_iff_le_vanishingOpen M ⊤).mp
      ((restrictFunctor (⊤ : X.Opens).ι).map_isZero h)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.ModuleVanishingOpen
