import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.ZariskiOpenCover
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.EndGluing
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Bundle Trivialization Sieve -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Base.BundleTrivializationSieve

noncomputable section

/-! A line bundle on a test base is trivial on a covering sieve of that test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (T : Over S) (L : Line.Bundles.LineBundle T.left)

def baseBundleTrivializationSieve : Sieve T where
  arrows U f := Nonempty ((L.pullback f.left).sheaf ≅ Line.Bundles.structureModule U.left)
  downward_closed := by
    intro U V f ⟨e⟩ g
    exact ⟨(Scheme.Modules.pullbackComp g.left f.left).symm.app L.sheaf ≪≫
      (Scheme.Modules.pullback g.left).mapIso e ≪≫ Line.Bundles.structureModulePullbackIso g.left⟩

theorem baseBundleTrivializationSieve_mem_zariski :
    baseBundleTrivializationSieve T L ∈ (Scheme.zariskiTopology.over S) T := by
  apply (Scheme.zariskiTopology.over S).superset_covering
    (S := Relative.ZariskiOpenCover.relativeOpenCoverSieve T (LineBundle.EndGluing.lineEndFrameCover L)) ?_
    (Relative.ZariskiOpenCover.relativeOpenCoverSieve_mem T (LineBundle.EndGluing.lineEndFrameCover L) (LineBundle.EndGluing.lineEndFrameCover_covers L))
  apply (Sieve.generate_le_iff _ _).mpr
  rintro U f ⟨i⟩
  exact ⟨i.frame.symm⟩

theorem baseBundleTrivializationSieve_mem_fppf :
    baseBundleTrivializationSieve T L ∈ (Scheme.fppfTopology.over S) T := by
  have h : Scheme.zariskiTopology ≤ Scheme.fppfTopology :=
    Precoverage.toGrothendieck_mono Scheme.zariskiPrecoverage_le_fppfPrecoverage
  exact h _ (baseBundleTrivializationSieve_mem_zariski T L)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Base.BundleTrivializationSieve
