import OAI.AlgebraicGeometry.FormalGeometry.Completion.Polarization.PicardMap
import Mathlib.CategoryTheory.Sites.Subsheaf
import Mathlib.CategoryTheory.Sites.SubcanonicalOver

/-! # Functor -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.Functor

noncomputable section

/-! The kernel of the actual polarization map is an fppf sheaf and
a subfunctor of the actual functor of points of the group scheme. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

namespace Construction

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
  (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)

def polarizationKernelSubfunctor : Subfunctor (yoneda.obj A) where
  obj T := { a | Polarization.PicardMap.Construction.polarizationRelativeSection A L a = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A T.unop }
  map j a ha :=
    (Polarization.PicardMap.Construction.polarizationRelativeSection_natural A L j.unop a).symm.trans
      ((congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A).obj.map j) ha).trans (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass_naturality A j.unop))

theorem polarizationKernelSubfunctor_isSheaf :
    Presieve.IsSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      (polarizationKernelSubfunctor A L).toFunctor := by
  let J := Scheme.fppfTopology.over (Spec (CommRingCat.of K))
  have hA := GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (J := J) (yoneda.obj A)
  apply ((polarizationKernelSubfunctor A L).isSheaf_iff hA).mpr
  intro T a hR
  have hP : Presieve.IsSheaf J (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A).obj :=
    (isSheaf_iff_isSheaf_of_type J (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A).obj).mp (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A).property
  apply (hP _ hR).isSeparatedFor.ext
  intro U j hj
  change Polarization.PicardMap.Construction.polarizationRelativeSection A L (j ≫ a) = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A U at hj
  exact (Polarization.PicardMap.Construction.polarizationRelativeSection_natural A L j a).trans
    (hj.trans (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass_naturality A j).symm)

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.Functor
