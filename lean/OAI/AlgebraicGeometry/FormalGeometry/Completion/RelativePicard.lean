import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PicardPullbackId

/-! # Relative Picard -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.RelativePicard

noncomputable section

/-! An actual line pulled back from the test scheme disappears in the
relative Picard sheaf, by open trivializations and fppf separatedness. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry _root_.CategoryTheory OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf Opposite _root_.TopologicalSpace
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

namespace Construction.RelativePicardBaseTwist

universe u
variable {S : Scheme.{u}}

def openObject (T : Over S) (U : T.left.Opens) : Over S := Over.mk (U.ι ≫ T.hom)

def openInclusion (T : Over S) (U : T.left.Opens) : openObject T U ⟶ T := Over.homMk U.ι

theorem openCover_mem (T : Over S) {I : Type u} (U : I → T.left.Opens) (hU : IsOpenCover U) :
    Sieve.ofArrows (fun i => openObject T (U i)) (fun i => openInclusion T (U i)) ∈
      (Scheme.fppfTopology.over S) T := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact (Precoverage.toGrothendieck_mono Scheme.zariskiPrecoverage_le_fppfPrecoverage)
    _ (T.left.openCoverOfIsOpenCover U hU).mem_grothendieckTopology

theorem sections_ext (T : Over S) (F : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)))
    {I : Type u} (U : I → T.left.Opens) (hU : IsOpenCover U) {x y : F.obj.obj (op T)}
    (h : ∀ i, F.obj.map (openInclusion T (U i)).op x = F.obj.map (openInclusion T (U i)).op y) : x = y := by
  let a : PUnit.{u + 2} ⟶ F.obj.obj (op T) := ↾(fun _ => x)
  let b : PUnit.{u + 2} ⟶ F.obj.obj (op T) := ↾(fun _ => y)
  have hab : a = b := F.property.hom_ext_ofArrows
    (fun i => openInclusion T (U i)) (openCover_mem T U hU) (by
      intro i
      apply ConcreteCategory.ext_apply
      intro z
      exact h i)
  exact congrArg (fun c => c PUnit.unit) hab

def baseTwist (A : Over S) {T : Over S} (m : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass T.left)
    (q : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).obj (op T)) : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).obj (op T) := by
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A).left at q ⊢
  exact AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (fst T A).left m * q

theorem baseTwist_natural (A : Over S) {T U : Over S} (h : U ⟶ T)
    (m : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass T.left) (q : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).obj (op T)) :
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).map h.op (baseTwist A m q) =
      baseTwist A (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass h.left m) ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).map h.op q) := by
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A).left at q
  change Quotients.FiniteDescent.PicardPullbackId.Construction.PicardPullback.map (h ⊗ₘ 𝟙 A).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (fst T A).left m * q) = _
  rw [map_mul]
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (h ⊗ₘ 𝟙 A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (fst T A).left m) * _ =
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (fst U A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass h.left m) * _
  rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]
  have he : (h ⊗ₘ 𝟙 A).left ≫ (fst T A).left = (fst U A).left ≫ h.left :=
    congrArg Over.Hom.left (tensorHom_fst h (𝟙 A))
  rw [he]
  rfl

theorem baseTwist_trivial (A : Over S) {T : Over S} (q : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).obj (op T)) :
    baseTwist A (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass T.left) q = q := by
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A).left at q
  unfold baseTwist
  rw [AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_trivial]
  exact one_mul q

theorem toRelativePicard_baseTwist (A : Over S) {T : Over S} (M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle T.left)
    (q : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).obj (op T)) :
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (op T) (baseTwist A (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M) q) =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (op T) q := by
  choose U hx he using M.locallyTrivial
  have hU : IsOpenCover U := by
    apply top_unique
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hx x⟩
  apply sections_ext T (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A) U hU
  intro i
  rw [← (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).naturality_apply, ← (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).naturality_apply]
  apply congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (op (openObject T (U i))))
  rw [baseTwist_natural]
  have hi : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (openInclusion T (U i)).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass (openObject T (U i)).left := Quotient.sound (he i)
  rw [hi, baseTwist_trivial]

theorem toRelativePicard_baseTwist_class (A : Over S) {T : Over S} (m : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass T.left)
    (q : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).obj (op T)) :
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (op T) (baseTwist A m q) = (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (op T) q := by
  induction m using Quotient.inductionOn with
  | h M => exact toRelativePicard_baseTwist A M q

end Construction.RelativePicardBaseTwist

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.RelativePicard
