import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.LocalIsomorphisms

/-! # Local Equality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.LocalEquality

noncomputable section

/-! Local actual bundle isomorphisms imply equality in the relative Picard sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem relativePicard_eq_of_local_bundle_iso {S : Scheme.{u}} (P T : Over S)
    (L M : Line.Bundles.LineBundle ((PicardSheaf.familySchemeFunctor P).obj T)) (R : Sieve T)
    (hR : R ∈ (Scheme.fppfTopology.over S) T)
    (hlocal : ∀ {U : Over S} (f : U ⟶ T), R f →
      Nonempty ((L.pullback ((PicardSheaf.familySchemeFunctor P).map f)).sheaf ≅
        (M.pullback ((PicardSheaf.familySchemeFunctor P).map f)).sheaf)) :
    (PicardSheaf.toRelativePicard P).app (.op T) (Line.Bundles.LineBundle.classOf L) =
      (PicardSheaf.toRelativePicard P).app (.op T) (Line.Bundles.LineBundle.classOf M) := by
  have hF := (isSheaf_iff_isSheaf_of_type _ _).mp (PicardSheaf.relativePicardSheaf P).property
  apply (hF R hR).isSeparatedFor.ext
  intro U f hf
  have h : (PicardSheaf.relativePicardPresheaf P).map f.op (Line.Bundles.LineBundle.classOf L) =
      (PicardSheaf.relativePicardPresheaf P).map f.op (Line.Bundles.LineBundle.classOf M) := Quotient.sound (hlocal f hf)
  exact (PicardSheaf.toRelativePicard_naturality P f (Line.Bundles.LineBundle.classOf L)).trans
    ((congrArg ((PicardSheaf.toRelativePicard P).app (.op U)) h).trans
      (PicardSheaf.toRelativePicard_naturality P f (Line.Bundles.LineBundle.classOf M)).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.LocalEquality
