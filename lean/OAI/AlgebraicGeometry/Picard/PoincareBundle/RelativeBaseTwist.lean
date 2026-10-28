import OAI.AlgebraicGeometry.Picard.PoincareBundle.Open.Locality
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.ClassUnits

/-! # Relative Base Twist -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.RelativeBaseTwist

noncomputable section

/-!
# Lines from the test scheme vanish in the relative Picard sheaf

The proof uses actual open trivializations and separatedness of fppf sheaves.
It does not assume a quotient presentation of the Picard functor.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.TopologicalSpace
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Bundles OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.LineBundles OAI.AlgebraicGeometry.Picard.PoincareBundle.Functor OAI.AlgebraicGeometry.Picard.PoincareBundle.Origin
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.ClassUnits OAI.AlgebraicGeometry.Picard.PoincareBundle.Open.Locality

variable {S : Scheme.{u}} (A : Over S)

/-- Tensoring a relative line class by a line class from the test scheme. -/
def baseTwist {T : Over S} (m : Line.Bundles.LineBundleClass T.left)
    (q : (Functor.relativePicardPresheaf A).obj (op T)) :
    (Functor.relativePicardPresheaf A).obj (op T) :=
  Tensor.LineBundles.tensorClass (Line.Bundles.LineBundleClass.pullback (fst T A).left m) q

/-- The base twist commutes with every change of test scheme. -/
theorem baseTwist_natural {T U : Over S} (h : U ⟶ T)
    (m : Line.Bundles.LineBundleClass T.left) (q : (Functor.relativePicardPresheaf A).obj (op T)) :
    (Functor.relativePicardPresheaf A).map h.op (baseTwist A m q) =
      baseTwist A (Line.Bundles.LineBundleClass.pullback h.left m)
        ((Functor.relativePicardPresheaf A).map h.op q) := by
  change Line.Bundles.LineBundleClass.pullback (h ⊗ₘ 𝟙 A).left
      (Tensor.LineBundles.tensorClass (Line.Bundles.LineBundleClass.pullback (fst T A).left m) q) =
    Tensor.LineBundles.tensorClass (Line.Bundles.LineBundleClass.pullback (fst U A).left (Line.Bundles.LineBundleClass.pullback h.left m)) _
  erw [Tensor.LineBundles.tensorClass_pullback, ← Line.Bundles.LineBundleClass.pullback_comp,
    ← Line.Bundles.LineBundleClass.pullback_comp]
  have hs : (h ⊗ₘ 𝟙 A).left ≫ (fst T A).left = (fst U A).left ≫ h.left :=
    congrArg Over.Hom.left (by simp : (h ⊗ₘ 𝟙 A) ≫ fst T A = fst U A ≫ h)
  rw [hs]
  rfl

/-- An actually trivial test-scheme factor already vanishes before sheafification. -/
theorem baseTwist_trivial {T : Over S} (q : (Functor.relativePicardPresheaf A).obj (op T)) :
    baseTwist A (Origin.trivialLineClass T.left) q = q := by
  dsimp only [baseTwist]
  erw [Origin.pullback_trivialLineClass, Tensor.ClassUnits.tensorClass_trivial_left]

/-- A test-scheme line twist has the same relative Picard section on a trivializing open. -/
theorem baseTwist_open {T : Over S} (M : Line.Bundles.LineBundle T.left)
    (q : (Functor.relativePicardPresheaf A).obj (op T)) (U : T.left.Opens)
    (e : (Scheme.Modules.pullback U.ι).obj M.sheaf ≅ Line.Bundles.unitLine U) :
    (Functor.relativePicardPresheaf A).map (Open.Locality.openInclusion T U).op (baseTwist A (Line.Bundles.LineBundleClass.mk M) q) =
      (Functor.relativePicardPresheaf A).map (Open.Locality.openInclusion T U).op q := by
  rw [baseTwist_natural]
  have he : Line.Bundles.LineBundleClass.pullback (Open.Locality.openInclusion T U).left (Line.Bundles.LineBundleClass.mk M) =
      Origin.trivialLineClass (Open.Locality.openObject T U).left := Quotient.sound ⟨e⟩
  rw [he, baseTwist_trivial]

/-- Every actual line bundle from the test scheme becomes trivial as a relative Picard twist. -/
theorem toRelativePicard_baseTwist {T : Over S} (M : Line.Bundles.LineBundle T.left)
    (q : (Functor.relativePicardPresheaf A).obj (op T)) :
    (Functor.toRelativePicard A).app (op T) (baseTwist A (Line.Bundles.LineBundleClass.mk M) q) =
      (Functor.toRelativePicard A).app (op T) q := by
  choose U hx he using M.isLine
  have hU : IsOpenCover U := by
    apply top_unique
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩
  apply Open.Locality.sections_ext T (Functor.relativePicardSheaf A) U hU
  intro i
  rw [← (Functor.toRelativePicard A).naturality_apply, ← (Functor.toRelativePicard A).naturality_apply]
  exact congrArg ((Functor.toRelativePicard A).app (op (Open.Locality.openObject T (U i))))
    (baseTwist_open A M q (U i) (he i).some)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.RelativeBaseTwist
