import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-! # Sheaf Local Epi -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Module.SheafLocalEpi.RingedModules

/-! Surjective section maps on arbitrarily small neighborhoods imply a module-sheaf epimorphism. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

variable {T : Type} [TopologicalSpace T]
  {R : Sheaf (Opens.grothendieckTopology T) RingCat.{0}}
  {M N : SheafOfModules.{0} R} (f : M ⟶ N)

theorem moduleSheaf_epi_of_localSurjective
    (hf : ∀ (O : Opens T) (p : O), ∃ W : Opens T, W ≤ O ∧ (p : T) ∈ W ∧
      Function.Surjective (f.val.app (op W))) : Epi f := by
  let F := SheafOfModules.toSheaf R
  have hl : Sheaf.IsLocallySurjective (F.map f) := by
    constructor
    intro O a p hp
    obtain ⟨W, hWO, hpW, hs⟩ := hf O ⟨p, hp⟩
    refine ⟨W, homOfLE hWO, ?_, hpW⟩
    exact hs (N.val.map (homOfLE hWO).op a)
  let : Sheaf.IsLocallySurjective (F.map f) := hl
  exact F.epi_of_epi_map inferInstance

end OAI.AlgebraicGeometry.Comparison.Betti.Module.SheafLocalEpi.RingedModules
