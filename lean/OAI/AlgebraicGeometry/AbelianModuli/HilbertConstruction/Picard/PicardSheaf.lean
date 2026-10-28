import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # Picard Sheaf -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf

noncomputable section

/-!
The underlying set-valued relative Picard sheaf. Its presheaf assigns to a
test scheme the isomorphism classes of actual line bundles on the base-changed
family; fppf sheafification removes locally trivial choices. No representing
scheme or existence theorem is assumed by this construction.
-/

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}}

/-- The total spaces of a family after varying its test scheme. -/
def familySchemeFunctor (X : Over S) : Over S ⥤ Scheme.{u} :=
  tensorRight X ⋙ Over.forget S

/-- Line-bundle classes on the base changes of a fixed family. -/
def relativePicardPresheaf (X : Over S) : (Over S)ᵒᵖ ⥤ Type (u + 1) :=
  (familySchemeFunctor X).op ⋙ Line.Bundles.lineBundleClassFunctor

/-- The underlying sheaf of sets of the relative fppf Picard sheaf. -/
def relativePicardSheaf (X : Over S) :
    Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).obj
    (relativePicardPresheaf X)

/-- The canonical map from actual line-bundle classes to the Picard sheaf. -/
def toRelativePicard (X : Over S) :
    relativePicardPresheaf X ⟶ (relativePicardSheaf X).obj :=
  toSheafify (Scheme.fppfTopology.over S) (relativePicardPresheaf X)

/-- A section of the Picard sheaf over the test scheme `T`. -/
abbrev PicardSections (X T : Over S) := (relativePicardSheaf X).obj.obj (.op T)

/-- The zero class comes from the trivial line bundle. -/
def trivialPicardClass (X T : Over S) : PicardSections X T :=
  (toRelativePicard X).app (.op T)
    (Line.Bundles.LineBundle.trivialClass ((familySchemeFunctor X).obj T))

theorem toRelativePicard_naturality (X : Over S) {T U : Over S} (f : U ⟶ T)
    (q : (relativePicardPresheaf X).obj (.op T)) :
    (relativePicardSheaf X).obj.map f.op ((toRelativePicard X).app (.op T) q) =
      (toRelativePicard X).app (.op U) ((relativePicardPresheaf X).map f.op q) :=
  ((toRelativePicard X).naturality_apply f.op q).symm

@[simp]
theorem trivialPicardClass_naturality (X : Over S) {T U : Over S} (f : U ⟶ T) :
    (relativePicardSheaf X).obj.map f.op (trivialPicardClass X T) =
      trivialPicardClass X U := by
  exact (toRelativePicard_naturality X f
    (Line.Bundles.LineBundle.trivialClass ((familySchemeFunctor X).obj T))).trans
      (congrArg (fun q : (relativePicardPresheaf X).obj (.op U) =>
        (toRelativePicard X).app (.op U) q)
        (Line.Bundles.LineBundle.pullbackClass_trivial ((familySchemeFunctor X).map f)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf
