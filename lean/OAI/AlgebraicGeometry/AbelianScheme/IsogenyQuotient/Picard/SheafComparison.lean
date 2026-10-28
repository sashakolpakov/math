import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LineClassComparison
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Functor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf

/-! # Sheaf Comparison -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Picard.SheafComparison.Construction

noncomputable section

/-! The PoincareBundle relative Picard sheaf is identified with the original HilbertConstruction
relative Picard sheaf by the actual line-class comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf

universe u

variable {S : Scheme.{u}} (A : Over S)

def e45RelativePicardPresheafIso : Picard.PoincareBundle.Functor.relativePicardPresheaf A ≅ AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A :=
  Functor.isoWhiskerLeft (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.familySchemeFunctor A).op LineClassComparison.Construction.e45LineClassFunctorIso

theorem e45RelativePicardPresheafIso_apply (T : Over S)
    (q : (Picard.PoincareBundle.Functor.relativePicardPresheaf A).obj (.op T)) :
    (e45RelativePicardPresheafIso A).hom.app (.op T) q = LineClassComparison.Construction.e45LineClassEquiv _ q := rfl

theorem e45RelativePicardPresheafIso_natural {T U : Over S} (f : U ⟶ T)
    (q : (Picard.PoincareBundle.Functor.relativePicardPresheaf A).obj (.op T)) :
    LineClassComparison.Construction.e45LineClassEquiv _ ((Picard.PoincareBundle.Functor.relativePicardPresheaf A).map f.op q) =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).map f.op (LineClassComparison.Construction.e45LineClassEquiv _ q) :=
  (e45RelativePicardPresheafIso A).hom.naturality_apply f.op q

def e45RelativePicardSheafIso : Picard.PoincareBundle.Functor.relativePicardSheaf A ≅ AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A :=
  (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).mapIso (e45RelativePicardPresheafIso A)

theorem e45RelativePicardSheafIso_toSheaf (T : Over S)
    (q : (Picard.PoincareBundle.Functor.relativePicardPresheaf A).obj (.op T)) :
    (e45RelativePicardSheafIso A).hom.hom.app (.op T) ((Picard.PoincareBundle.Functor.toRelativePicard A).app (.op T) q) =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (.op T) (LineClassComparison.Construction.e45LineClassEquiv _ q) := by
  exact (congrArg (fun f => f.app (.op T) q)
    (toSheafify_naturality (Scheme.fppfTopology.over S) (e45RelativePicardPresheafIso A).hom)).symm

theorem e45RelativePicardSection_eq_iff (T : Over S)
    (q r : (Picard.PoincareBundle.Functor.relativePicardPresheaf A).obj (.op T)) :
    (Picard.PoincareBundle.Functor.toRelativePicard A).app (.op T) q = (Picard.PoincareBundle.Functor.toRelativePicard A).app (.op T) r ↔
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (.op T) (LineClassComparison.Construction.e45LineClassEquiv _ q) =
        (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (.op T) (LineClassComparison.Construction.e45LineClassEquiv _ r) := by
  have h := (((sheafToPresheaf _ _).mapIso (e45RelativePicardSheafIso A)).app (.op T)).toEquiv.injective
  rw [← e45RelativePicardSheafIso_toSheaf, ← e45RelativePicardSheafIso_toSheaf]
  exact ⟨congrArg _, fun he => h he⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Picard.SheafComparison.Construction
