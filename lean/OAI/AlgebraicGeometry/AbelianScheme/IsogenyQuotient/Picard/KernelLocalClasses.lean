import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AffineSieveCover
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledGroup
import OAI.AlgebraicGeometry.Picard.Homomorphisms.SheafMaps
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-! # Kernel Local Classes -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Picard.KernelLocalClasses.Construction

noncomputable section

/-! Every Picard pullback-kernel section is locally represented by an
actual line class whose pullback is trivial, with affine test domains. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.Homomorphisms.SheafMaps.Construction OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard

universe u
variable {S : Scheme.{u}} {A B : Over S} [GrpObj B] (f : A ⟶ B)

set_option backward.isDefEq.respectTransparency false in
theorem picardPullbackKernel_cover_of_class_lifts
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
          ((Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.map a.op y) → R a) :
    R ∈ (Scheme.fppfTopology.over S) T := by
  let J := Scheme.fppfTopology.over S
  have : Presheaf.IsLocallySurjective J (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard B) :=
    inferInstanceAs (Presheaf.IsLocallySurjective J (toSheafify J (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf B)))
  have : Presheaf.IsLocallyInjective J (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A) :=
    inferInstanceAs (Presheaf.IsLocallyInjective J (toSheafify J (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A)))
  let z := (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheafInclusion B).hom.app (op T) y
  apply J.transitive (Presheaf.imageSieve_mem J (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard B) z)
  intro U a ha
  obtain ⟨c, hc⟩ := ha
  have hz : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (op U)
      ((Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullbackPresheaf f).app (op U) c) = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A U := by
    rw [← Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullback_toRelativePicard_apply, hc]
    exact ((Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullback f).hom.naturality_apply a.op z).trans
      ((congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A).obj.map a.op) hy).trans
        (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass_naturality A a))
  apply J.transitive (Presheaf.equalizerSieve_mem J (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A)
    ((Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullbackPresheaf f).app (op U) c)
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.familySchemeFunctor A).obj U)) hz)
  intro V b hb
  apply AffineSieveCover.Construction.fppfSieve_mem_of_affine_arrows
  intro W _ t
  let cW := (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf B).map (t ≫ b).op c
  have hzero : (Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullbackPresheaf f).app (op W) cW =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.familySchemeFunctor A).obj W) := by
    rw [show cW = (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf B).map (t ≫ b).op c from rfl,
      (Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullbackPresheaf f).naturality_apply]
    change (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).map b.op
      ((Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullbackPresheaf f).app (op U) c) =
        (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).map b.op
          (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.familySchemeFunctor A).obj U)) at hb
    rw [op_comp, Functor.map_comp]
    change (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).map t.op
      ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).map b.op ((Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullbackPresheaf f).app (op U) c)) = _
    rw [hb]
    exact (congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).map t.op)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_trivial ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.familySchemeFunctor A).map b))).trans
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_trivial ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.familySchemeFunctor A).map t))
  apply h W ((t ≫ b) ≫ a) cW hzero
  rw [show cW = (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf B).map (t ≫ b).op c from rfl,
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard B).naturality_apply, hc]
  have hmap := (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf B).obj.map_comp_apply a.op (t ≫ b).op z
  exact hmap.symm.trans
    ((Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheafInclusion B).hom.naturality_apply (((t ≫ b) ≫ a).op) y).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Picard.KernelLocalClasses.Construction
