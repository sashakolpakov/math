import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.OpenMapGluing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.ModuleIsomorphisms

/-! # Open Isomorphism Gluing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module

noncomputable section

/-! Compatible local module isomorphisms glue to an actual global isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {X : Scheme.{u}} {ι : Type v} {U : ι → X.Opens} {M N : X.Modules}
variable (D : OpenMapGluing.OpenCoverModuleMaps U M N) (hU : ∀ x : X, ∃ i, x ∈ U i)

theorem OpenMapGluing.OpenCoverModuleMaps.glue_isIso (hD : ∀ i, IsIso (D.localMap i)) : IsIso (D.glue hU) := by
  apply Local.ModuleIsomorphisms.moduleMap_isIso_of_locally
  intro x
  obtain ⟨i, hi⟩ := hU x
  refine ⟨U i, hi, ?_⟩
  apply (Power.Nonvanishing.isIso_restrict_map_iff (U i).ι (D.glue hU)).mp
  rw [D.glue_restrict hU i]
  exact hD i

def OpenMapGluing.OpenCoverModuleMaps.glueIso (hD : ∀ i, IsIso (D.localMap i)) : M ≅ N :=
  @asIso X.Modules _ M N (D.glue hU) (D.glue_isIso hU hD)

theorem OpenMapGluing.OpenCoverModuleMaps.glueIso_restrict (hD : ∀ i, IsIso (D.localMap i)) (i : ι) :
    (Scheme.Modules.restrictFunctor (U i).ι).map (D.glueIso hU hD).hom = D.localMap i :=
  D.glue_restrict hU i

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module
