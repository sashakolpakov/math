import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-! # Local Isomorphisms -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.LocalIsomorphisms

noncomputable section

/-! Equality in the relative Picard sheaf yields actual line-bundle isomorphisms on a covering sieve. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}}

def picardBundleIsoSieve (X T : Over S)
    (L M : Line.Bundles.LineBundle ((PicardSheaf.familySchemeFunctor X).obj T)) : Sieve T :=
  Presheaf.equalizerSieve (F := PicardSheaf.relativePicardPresheaf X)
    (X := .op T) (Line.Bundles.LineBundle.classOf L) (Line.Bundles.LineBundle.classOf M)

theorem picardBundleIsoSieve_apply (X T : Over S)
    (L M : Line.Bundles.LineBundle ((PicardSheaf.familySchemeFunctor X).obj T)) {U : Over S} (f : U ⟶ T) :
    picardBundleIsoSieve X T L M f ↔
      Nonempty ((L.pullback ((PicardSheaf.familySchemeFunctor X).map f)).sheaf ≅
        (M.pullback ((PicardSheaf.familySchemeFunctor X).map f)).sheaf) :=
  Quotient.eq

theorem picardBundleIsoSieve_mem_of_class_eq (X T : Over S)
    (L M : Line.Bundles.LineBundle ((PicardSheaf.familySchemeFunctor X).obj T))
    (h : (PicardSheaf.toRelativePicard X).app (.op T) (Line.Bundles.LineBundle.classOf L) =
      (PicardSheaf.toRelativePicard X).app (.op T) (Line.Bundles.LineBundle.classOf M)) :
    picardBundleIsoSieve X T L M ∈ (Scheme.fppfTopology.over S) T := by
  exact Presheaf.equalizerSieve_mem (Scheme.fppfTopology.over S)
    (toSheafify (Scheme.fppfTopology.over S) (PicardSheaf.relativePicardPresheaf X))
    (Line.Bundles.LineBundle.classOf L) (Line.Bundles.LineBundle.classOf M) h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.LocalIsomorphisms
