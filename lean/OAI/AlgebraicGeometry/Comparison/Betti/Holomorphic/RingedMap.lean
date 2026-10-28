import OAI.AlgebraicGeometry.Comparison.Betti.ManifoldHolomorphicModuleSheaf

/-! # Ringed Map -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.RingedMap

noncomputable section

/-! The actual pullback of holomorphic functions gives a morphism of the native ringed spaces. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

variable {E F M N : Type}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]
  (g : M → N) (hg : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ g)

def manifoldHolomorphicStructureMap :
    ManifoldHolomorphicModuleSheaf.manifoldHolomorphicStructureSheaf F N ⟶
      (TopCat.Sheaf.pushforward RingCat (TopCat.ofHom ⟨g, hg.continuous⟩)).obj
        (ManifoldHolomorphicModuleSheaf.manifoldHolomorphicStructureSheaf E M) where
  hom.app U := RingCat.ofHom
    ((ContMDiff.smoothSheafCommRingHom (I := 𝓘(ℂ)) (R := ℂ)
      (IP := 𝓘(ℂ, F)) (P := N) g hg).hom.app U).hom
  hom.naturality := by
    intro U V i
    apply RingCat.hom_ext
    apply RingHom.ext
    intro a
    apply ContMDiffMap.ext
    intro x
    rfl

theorem manifoldHolomorphicStructureMap_apply (U : Opens N)
    (a : C^∞⟮𝓘(ℂ, F), U; 𝓘(ℂ), ℂ⟯)
    (x : (Opens.map (TopCat.ofHom ⟨g, hg.continuous⟩)).obj U) :
    (show C^∞⟮𝓘(ℂ, E), (Opens.map (TopCat.ofHom ⟨g, hg.continuous⟩)).obj U; 𝓘(ℂ), ℂ⟯ from
      (manifoldHolomorphicStructureMap g hg).hom.app (op U) a) x =
      a ⟨g x, x.property⟩ := rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.RingedMap
