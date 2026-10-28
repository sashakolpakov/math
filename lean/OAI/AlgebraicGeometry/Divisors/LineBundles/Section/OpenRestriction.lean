import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Open Restriction -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Section.OpenRestriction.BundleCycles

noncomputable section

/-! # LineBundleCycles: the actual restricted section on compatible open neighborhoods -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Scheme.{0}} (p : Y ⟶ X) (s : X ⟶ Y) (hs : s ≫ p = 𝟙 X)
    (U : Y.Opens) (V : X.Opens) (hV : V ≤ s ⁻¹ᵁ U) (hU : U ≤ p ⁻¹ᵁ V)

def sectionOpenProjection : U.toScheme ⟶ V.toScheme := Y.homOfLE hU ≫ morphismRestrict p V

def sectionOpenMap : V.toScheme ⟶ U.toScheme := X.homOfLE hV ≫ morphismRestrict s U

theorem sectionOpenProjection_ι : sectionOpenProjection p U V hU ≫ V.ι = U.ι ≫ p := by
  change (Y.homOfLE hU ≫ morphismRestrict p V) ≫ V.ι = _
  rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]

theorem sectionOpenMap_ι : sectionOpenMap s U V hV ≫ U.ι = V.ι ≫ s := by
  change (X.homOfLE hV ≫ morphismRestrict s U) ≫ U.ι = _
  rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]

include hs in
theorem sectionOpen_retraction : sectionOpenMap s U V hV ≫ sectionOpenProjection p U V hU = 𝟙 V.toScheme := by
  apply (cancel_mono V.ι).mp
  rw [Category.assoc, sectionOpenProjection_ι, ← Category.assoc, sectionOpenMap_ι,
    Category.assoc, hs, Category.comp_id, Category.id_comp]

include hs hU hV in
theorem sectionOpen_preimage : s ⁻¹ᵁ U = V := by
  apply le_antisymm _ hV
  intro x hx
  have hy := hU hx
  change p (s x) ∈ V at hy
  have he : p (s x) = x := congrArg (fun f => f x) hs
  exact he ▸ hy

instance sectionOpenProjection_smooth [Smooth p] : Smooth (sectionOpenProjection p U V hU) := by
  change Smooth (Y.homOfLE hU ≫ morphismRestrict p V)
  infer_instance

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Section.OpenRestriction.BundleCycles
