import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapCoverEquality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.GlobalSectionsDetectMaps

/-! # Epimorphism Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.EpimorphismCover

noncomputable section

/-! Epimorphisms of modules can be checked on an open cover, using global sections when the covering opens are affine and the target is quasicoherent. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

theorem module_epi_of_restrict_cover {X : Scheme.{u}} {ι : Type v} (U : ι → X.Opens)
    (hU : ∀ x : X, ∃ i, x ∈ U i) {M N : X.Modules} (f : M ⟶ N)
    (hf : ∀ i, Epi ((Scheme.Modules.restrictFunctor (U i).ι).map f)) : Epi f := by
  constructor
  intro P g h hcomp
  apply MapCoverEquality.moduleMap_eq_of_restrict_cover U hU
  intro i
  have := hf i
  apply (cancel_epi ((Scheme.Modules.restrictFunctor (U i).ι).map f)).mp
  simpa only [← Functor.map_comp] using congrArg (Scheme.Modules.restrictFunctor (U i).ι).map hcomp

theorem module_epi_of_affine_cover_section_surjective {X : Scheme.{u}} {ι : Type v}
    (U : ι → X.Opens) (hU : ∀ x : X, ∃ i, x ∈ U i) (hA : ∀ i, IsAffineOpen (U i))
    {M N : X.Modules} [N.IsQuasicoherent] (f : M ⟶ N)
    (hf : ∀ i, Function.Surjective (f.app (U i))) : Epi f := by
  apply module_epi_of_restrict_cover U hU f
  intro i
  have : IsAffine (U i).toScheme := hA i
  apply Affine.GlobalSectionsDetectMaps.module_epi_of_affine_globalSections_surjective
  have hs : Function.Surjective (f.app ((U i).ι ''ᵁ ⊤)) := by
    rw [(U i).ι_image_top]
    exact hf i
  exact hs

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.EpimorphismCover
