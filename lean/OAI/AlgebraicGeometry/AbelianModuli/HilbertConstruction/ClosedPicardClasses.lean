import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFppfCovers
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.LocalIsomorphisms

/-! # Closed Picard Classes -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedPicardClasses

noncomputable section

/-! At an algebraically closed field point, equality of relative Picard classes is equality of actual bundle classes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K]

theorem toRelativePicard_injective_at_algClosed (X : Over S) (s : Spec (.of K) ⟶ S) :
    Function.Injective ((Picard.PicardSheaf.toRelativePicard X).app (.op (Over.mk s))) := by
  intro q r h
  apply (Presheaf.equalizerSieve_eq_top_iff (F := Picard.PicardSheaf.relativePicardPresheaf X)
    (X := .op (Over.mk s)) q r).mp
  exact ClosedFppfCovers.algClosed_over_fppf_cover_eq_top s _
    (Presheaf.equalizerSieve_mem (Scheme.fppfTopology.over S)
      (toSheafify (Scheme.fppfTopology.over S) (Picard.PicardSheaf.relativePicardPresheaf X)) q r h)

theorem picard_bundle_iso_of_class_eq_at_algClosed (X : Over S) (s : Spec (.of K) ⟶ S)
    (L M : Line.Bundles.LineBundle ((Picard.PicardSheaf.familySchemeFunctor X).obj (Over.mk s)))
    (h : (Picard.PicardSheaf.toRelativePicard X).app (.op (Over.mk s)) (Line.Bundles.LineBundle.classOf L) =
      (Picard.PicardSheaf.toRelativePicard X).app (.op (Over.mk s)) (Line.Bundles.LineBundle.classOf M)) :
    Nonempty (L.sheaf ≅ M.sheaf) :=
  Quotient.exact (toRelativePicard_injective_at_algClosed X s h)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedPicardClasses
