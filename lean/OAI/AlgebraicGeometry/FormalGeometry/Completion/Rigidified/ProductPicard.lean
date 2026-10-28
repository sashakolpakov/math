import OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.ProductComparisonNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf
import Mathlib.CategoryTheory.Sites.SubcanonicalOver

/-! # Product Picard -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified

noncomputable section

/-! An actual rigidified product line determines a natural Picard
map. Its zero fiber is an fppf sheaf on arbitrary test schemes. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u
variable {K : Type u} [Field K] {A B : Over (Spec (.of K))} [GrpObj A]
  (D : ProductLine.Construction.RigidifiedProductLine A B)

def ProductLine.Construction.RigidifiedProductLine.relativeValue {T : Over (Spec (.of K))} (a : T ⟶ B) : AbelianModuli.HilbertConstruction.Picard.PicardSheaf.PicardSections A T :=
  (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (op T) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line a))

theorem ProductLine.Construction.RigidifiedProductLine.relativeValue_natural {T U : Over (Spec (.of K))} (j : U ⟶ T) (a : T ⟶ B) :
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A).obj.map j.op (D.relativeValue a) = D.relativeValue (j ≫ a) := by
  unfold ProductLine.Construction.RigidifiedProductLine.relativeValue
  rw [← (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).naturality_apply]
  change (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (op U)
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (j ⊗ₘ 𝟙 A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line a))) = _
  rw [D.line_class_pullback]

def ProductLine.Construction.RigidifiedProductLine.zeroSubfunctor : Subfunctor (yoneda.obj B) where
  obj T := { a | D.relativeValue a = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A T.unop }
  map j a ha := (D.relativeValue_natural j.unop a).symm.trans
    ((congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A).obj.map j) ha).trans (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass_naturality A j.unop))

theorem ProductLine.Construction.RigidifiedProductLine.zeroSubfunctor_isSheaf :
    Presieve.IsSheaf (Scheme.fppfTopology.over (Spec (.of K))) D.zeroSubfunctor.toFunctor := by
  let J := Scheme.fppfTopology.over (Spec (.of K))
  have hB := GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (J := J) (yoneda.obj B)
  apply (D.zeroSubfunctor.isSheaf_iff hB).mpr
  intro T a hR
  have hP : Presieve.IsSheaf J (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A).obj :=
    (isSheaf_iff_isSheaf_of_type J (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A).obj).mp (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A).property
  apply (hP _ hR).isSeparatedFor.ext
  intro U j hj
  change D.relativeValue (j ≫ a) = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A U at hj
  exact (D.relativeValue_natural j a).trans (hj.trans (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass_naturality A j).symm)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified
