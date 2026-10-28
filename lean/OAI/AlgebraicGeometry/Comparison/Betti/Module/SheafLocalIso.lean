import OAI.AlgebraicGeometry.Comparison.Betti.Module.SheafLocalEpi
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization

/-! # Sheaf Local Iso -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Module.SheafLocalIso.RingedModules

/-! Bijective section maps on arbitrarily small neighborhoods determine a module-sheaf isomorphism. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

variable {T : Type} [TopologicalSpace T]
  {R : Sheaf (Opens.grothendieckTopology T) RingCat.{0}}
  {M N : SheafOfModules.{0} R} (f : M ⟶ N)

theorem moduleSheaf_isIso_of_localBijective
    (hf : ∀ (O : Opens T) (p : O), ∃ W : Opens T, W ≤ O ∧ (p : T) ∈ W ∧
      Function.Bijective (f.val.app (op W))) : IsIso f := by
  let F := SheafOfModules.toSheaf R
  have hi : Sheaf.IsLocallyInjective (F.map f) := by
    constructor
    intro O a b hab p hp
    obtain ⟨W, hWO, hpW, hs⟩ := hf O.unop ⟨p, hp⟩
    refine ⟨W, homOfLE hWO, ?_, hpW⟩
    change M.val.map (homOfLE hWO).op a = M.val.map (homOfLE hWO).op b
    apply hs.1
    exact (PresheafOfModules.naturality_apply f.val (homOfLE hWO).op a).trans
      ((congrArg (N.val.map (homOfLE hWO).op) hab).trans
        (PresheafOfModules.naturality_apply f.val (homOfLE hWO).op b).symm)
  have hs : Sheaf.IsLocallySurjective (F.map f) := by
    constructor
    intro O a p hp
    obtain ⟨W, hWO, hpW, hs⟩ := hf O ⟨p, hp⟩
    refine ⟨W, homOfLE hWO, ?_, hpW⟩
    exact hs.2 (N.val.map (homOfLE hWO).op a)
  have : IsIso (F.map f) := (Sheaf.isLocallyBijective_iff_isIso _).mp ⟨hi, hs⟩
  exact isIso_of_reflects_iso f F

end OAI.AlgebraicGeometry.Comparison.Betti.Module.SheafLocalIso.RingedModules
