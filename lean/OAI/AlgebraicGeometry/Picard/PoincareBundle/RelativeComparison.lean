import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Functor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf

/-! # Relative Comparison -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.RelativeComparison

noncomputable section

/-! The PoincareBundle relative Picard sheaf is the shared geometric Picard sheaf, by actual line-class comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle

variable {S : Scheme.{u}} (A : Over S)

/-- The line-class comparison is an isomorphism of the actual relative Picard presheaves. -/
def presheafIso : Functor.relativePicardPresheaf A ≅ AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A :=
  NatIso.ofComponents (fun T => (Line.Comparison.Bundle.classEquiv (T.unop ⊗ A).left).toIso) (by
    intro T U f
    apply ConcreteCategory.ext_apply
    intro q
    exact Line.Comparison.Bundle.classEquiv_pullback ((Functor.familySchemeFunctor A).map f.unop) q)

/-- Sheafification identifies the two relative Picard sheaves. -/
def sheafIso : Functor.relativePicardSheaf A ≅ AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A :=
  (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).mapIso (presheafIso A)

/-- The actual comparison commutes with the maps from geometric line classes to their sheafifications. -/
theorem toRelativePicard_comparison :
    Functor.toRelativePicard A ≫ (sheafIso A).hom.hom =
      (presheafIso A).hom ≫ AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A :=
  (toSheafify_naturality (Scheme.fppfTopology.over S) (presheafIso A).hom).symm

/-- The comparison acts on a represented line class by the same actual sheaf. -/
theorem section_comparison {T : Over S} (q : (Functor.relativePicardPresheaf A).obj (op T)) :
    (sheafIso A).hom.hom.app (op T) ((Functor.toRelativePicard A).app (op T) q) =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (op T) (Line.Comparison.Bundle.classEquiv (T ⊗ A).left q) :=
  congrArg (fun t => t.app (op T) q) (toRelativePicard_comparison A)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.RelativeComparison
