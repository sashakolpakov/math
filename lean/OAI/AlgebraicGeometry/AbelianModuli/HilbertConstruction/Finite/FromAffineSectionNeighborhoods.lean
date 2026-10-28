import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.FiniteGeneratingSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RestrictionGeneratingSections

/-! # From Affine Section Neighborhoods -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FromAffineSectionNeighborhoods

noncomputable section

/-! Finite section modules on affine neighborhoods give a finite-type sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules _root_.TopologicalSpace

universe u

theorem module_finiteType_of_affine_section_neighborhoods {X : Scheme.{u}}
    (M : X.Modules) [M.IsQuasicoherent]
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ IsAffineOpen U ∧
      Module.Finite Γ(U.toScheme, ⊤) Γ(M.restrict U.ι, ⊤)) :
    M.IsFiniteType := by
  choose U hx hU hfinite using h
  choose G hG using fun x : X ↦ by
    have : IsAffine (U x).toScheme := hU x
    have : Module.Finite Γ((U x).toScheme, ⊤) Γ(M.restrict (U x).ι, ⊤) := hfinite x
    exact Affine.FiniteGeneratingSections.affine_exists_finite_generatingSections (M.restrict (U x).ι)
  let q : M.LocalGeneratorsData :=
    { I := X
      X := U
      coversTop := by
        rw [Opens.coversTop_iff, IsOpenCover]
        apply top_le_iff.mp
        intro x _
        exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩
      generators := fun x ↦ RestrictionGeneratingSections.generatingSectionsOverOfRestrict M (U x) (G x) }
  have hq : q.IsFiniteType := by
    constructor
    intro x
    have : (G x).IsFiniteType := hG x
    exact RestrictionGeneratingSections.generatingSectionsOverOfRestrict_isFiniteType M (U x) (G x)
  have hqShrink : q.shrink.IsFiniteType := by
    constructor
    intro i
    dsimp [SheafOfModules.LocalGeneratorsData.shrink]
    exact hq.isFiniteType i.2.choose
  refine { exists_localGeneratorsData := ?_ }
  exact ⟨q.shrink, hqShrink⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FromAffineSectionNeighborhoods
