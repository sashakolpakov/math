import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.ZariskiOpenCover
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapSliceComposition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Gluing

/-! # Iso Sieve -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.IsoSieve

noncomputable section

/-! The test schemes where two line bundles become isomorphic form a covering Zariski sieve. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} (L M : Line.Bundles.LineBundle X) (T : Over X)

def lineBundleIsoSieve : Sieve T where
  arrows Y _ := Nonempty ((L.pullback Y.hom).sheaf ≅ (M.pullback Y.hom).sheaf)
  downward_closed := by
    intro Y Z f ⟨e⟩ g
    change (Scheme.Modules.pullback Y.hom).obj L.sheaf ≅
      (Scheme.Modules.pullback Y.hom).obj M.sheaf at e
    have : IsIso (Module.MapSlicePullback.moduleMapPullbackAlong g e.hom) := Module.MapSliceComposition.moduleMapPullbackAlong_isIso g e.hom
    let d : (Scheme.Modules.pullback Z.hom).obj L.sheaf ≅
        (Scheme.Modules.pullback Z.hom).obj M.sheaf := asIso (Module.MapSlicePullback.moduleMapPullbackAlong g e.hom)
    exact ⟨d⟩

theorem lineBundleIsoSieve_mem_zariski :
    lineBundleIsoSieve L M T ∈ (Scheme.zariskiTopology.over X) T := by
  let U := TensorPower.Gluing.tensorFrameCover (L.pullback T.hom) (M.pullback T.hom)
  have hU := TensorPower.Gluing.tensorFrameCover_covers (L.pullback T.hom) (M.pullback T.hom)
  apply (Scheme.zariskiTopology.over X).superset_covering
    (S := Relative.ZariskiOpenCover.relativeOpenCoverSieve T U) ?_ (Relative.ZariskiOpenCover.relativeOpenCoverSieve_mem T U hU)
  apply (Sieve.generate_le_iff _ _).mpr
  rintro Y f ⟨i⟩
  exact ⟨(Scheme.Modules.pullbackComp i.openSet.ι T.hom).symm.app L.sheaf ≪≫
    i.leftFrame.symm ≪≫ i.rightFrame ≪≫
    (Scheme.Modules.pullbackComp i.openSet.ι T.hom).app M.sheaf⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.IsoSieve
