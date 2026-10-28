import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.QuasicoherenceLocality

/-! # Quasicoherence Neighborhoods -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.QuasicoherenceNeighborhoods

noncomputable section

/-! Quasicoherence is detected on a chosen affine neighborhood of every point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

theorem module_quasicoherent_of_affine_neighborhoods {X : Scheme.{u}} (M : X.Modules)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ IsAffineOpen U ∧ (M.restrict U.ι).IsQuasicoherent) :
    M.IsQuasicoherent := by
  choose U hx hU hM using h
  have hlocal (x : X) : (M.over (U x)).IsQuasicoherent := by
    have : IsAffine (U x).toScheme := hU x
    have := hM x
    exact QuasicoherenceLocality.module_over_quasicoherent_of_affine_restriction M (U x)
  have hcover : (Opens.grothendieckTopology X).CoversTop U := by
    rw [Opens.coversTop_iff, IsOpenCover]
    apply top_le_iff.mp
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hx x⟩
  exact @SheafOfModules.IsQuasicoherent.of_coversTop _ _ _ _ _ _ _ _ M _ U hcover hlocal

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.QuasicoherenceNeighborhoods
