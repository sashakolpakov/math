import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Picard.KernelLocalClasses
import Mathlib.CategoryTheory.Sites.Closed

/-! # Kernel Local Class Covers -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Picard.KernelLocalClassCovers.Construction

noncomputable section

/-! The local class-lifting criterion also accepts a covering sieve
over each actual pullback-trivial line class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

theorem picardPullbackKernel_cover_of_local_class_lifts
    {S : Scheme.{u}} {A B : Over S} [GrpObj B] (f : A ⟶ B)
    (T : Over S) (y : (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.obj (op T))
    (hy : (Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullback f).hom.app (op T)
      ((Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheafInclusion B).hom.app (op T) y) = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A T)
    (R : Sieve T)
    (h : ∀ (U : Over S) [IsAffine U.left] (a : U ⟶ T)
      (c : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf B).obj (op U)),
      (Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullbackPresheaf f).app (op U) c =
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.familySchemeFunctor A).obj U) →
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard B).app (op U) c =
        (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheafInclusion B).hom.app (op U)
          ((Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.map a.op y) →
      R.pullback a ∈ (Scheme.fppfTopology.over S) U) :
    R ∈ (Scheme.fppfTopology.over S) T := by
  let J := Scheme.fppfTopology.over S
  have hclose : J.close R ∈ J T :=
    KernelLocalClasses.Construction.picardPullbackKernel_cover_of_class_lifts f T y hy (J.close R) h
  exact J.transitive hclose R (fun _ _ ha => ha)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Picard.KernelLocalClassCovers.Construction
