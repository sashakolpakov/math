import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.QuasicoherentEpimorphisms

/-! # Quasicoherent Epimorphisms -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineOpen.QuasicoherentEpimorphisms

noncomputable section

/-! Quasicoherent epimorphisms are surjective on sections of every affine open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules

universe u

theorem affineOpen_quasicoherent_surjective_of_epi {X : Scheme.{u}}
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : M ⟶ N) [Epi f] (U : X.Opens) (hU : IsAffineOpen U) :
    Function.Surjective (f.app U) := by
  have : IsAffine U.toScheme := hU
  have hs : Function.Surjective (f.app (U.ι ''ᵁ (⊤ : U.toScheme.Opens))) :=
    Affine.QuasicoherentEpimorphisms.quasicoherent_affine_surjective_of_epi ((restrictFunctor U.ι).map f)
  rw [U.ι_image_top] at hs
  exact hs

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineOpen.QuasicoherentEpimorphisms
