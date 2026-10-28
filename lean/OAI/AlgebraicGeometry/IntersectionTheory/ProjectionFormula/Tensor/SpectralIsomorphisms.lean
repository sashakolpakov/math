import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.SpectralObject
import Mathlib.Algebra.Homology.SpectralObject.Page

/-! # Spectral Isomorphisms -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.SpectralIsomorphisms

noncomputable section

/-! Isomorphisms of the underlying filtered complexes induce isomorphisms
on native relative homology and spectral terms. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.ComposableArrows

variable (R : Type) [CommRing R] (K : CochainComplex (ModuleCat.{0} R) ℤ)
  {ι : Type*} [Category* ι] (D : ι ⥤ CochainComplex (ModuleCat.{0} R) ℤ)

theorem term_map_isIso {F G : ComposableArrows ι 1} (α : F ⟶ G)
    (h : ∀ i, IsIso (D.map (α.app i))) (n : ℤ) :
    IsIso (((Tensor.SpectralObject.abelian R K D).H n).map α) := by
  let : ∀ i, IsIso (((D.mapComposableArrows 1).map α).app i) := h
  let : IsIso ((D.mapComposableArrows 1).map α) := NatIso.isIso_of_isIso_app _
  change IsIso ((HomotopyCategory.homologyFunctor (ModuleCat.{0} R) (.up ℤ) n).map
    ((Homotopy.homotopyFunctor R K).map ((HomotopyCategory.quotient _ _).map
      ((HomotopyCategory.composableArrowsFunctor (ModuleCat.{0} R)).map
        ((D.mapComposableArrows 1).map α)))))
  infer_instance

theorem E_map_isIso {i j k l i' j' k' l' : ι}
    (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
    (g₁ : i' ⟶ j') (g₂ : j' ⟶ k') (g₃ : k' ⟶ l')
    (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ g₁ g₂ g₃)
    (h : ∀ t, IsIso (D.map (α.app t))) (n : ℤ) :
    IsIso ((Tensor.SpectralObject.abelian R K D).map f₁ f₂ f₃ g₁ g₂ g₃ α (n - 1) n (n + 1)) := by
  apply Abelian.SpectralObject.isIso_map
  · apply term_map_isIso
    intro t
    fin_cases t
    · exact h 2
    · exact h 3
  · apply term_map_isIso
    intro t
    fin_cases t
    · exact h 1
    · exact h 2
  · apply term_map_isIso
    intro t
    fin_cases t
    · exact h 0
    · exact h 1

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.SpectralIsomorphisms
