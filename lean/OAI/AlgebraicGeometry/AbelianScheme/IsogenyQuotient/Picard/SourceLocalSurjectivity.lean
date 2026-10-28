import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.SourceMap
import OAI.AlgebraicGeometry.FormalGeometry.Completion.FppfPairLift

/-! # Source Local Surjectivity -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Picard.SourceLocalSurjectivity.Construction

noncomputable section

/-! The actual fppf source map makes Picard pullback from the abelian
image locally surjective, using only the original source dual. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

universe u
variable {S : Scheme.{u}} {A B C : Over S} [GrpObj A] [GrpObj B]
  (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (f : A ⟶ B) [IsMonHom f]
  (i : uliftYoneda.{u + 1}.obj C ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj)
  [Flat (PicardImage.SourceMap.Construction.picardImageSourceMap D f i).left] [Surjective (PicardImage.SourceMap.Construction.picardImageSourceMap D f i).left]
  [LocallyOfFinitePresentation (PicardImage.SourceMap.Construction.picardImageSourceMap D f i).left]

include D in
theorem picardImageSource_pullback_locallySurjective :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
      (i ≫ (Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullback A B f).hom) := by
  constructor
  intro T y
  let t := D.representable.homEquiv.symm y
  obtain ⟨U, a, x, _z, haf, has, hap, hx, _hz⟩ :=
    FormalGeometry.Completion.FppfPairLift.Construction.fppf_lift_pair (PicardImage.SourceMap.Construction.picardImageSourceMap D f i) t t
  have : Flat a.left := haf
  have : Surjective a.left := has
  have : LocallyOfFinitePresentation a.left := hap
  apply (Scheme.fppfTopology.over S).superset_covering _ (FormalGeometry.Completion.FppfSheafSectionDescent.Construction.fppfSingleton_cover a)
  apply (Sieve.generate_le_iff _ _).mpr
  intro V b hb
  cases hb
  refine ⟨ULift.up x, ?_⟩
  change (Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullback A B f).hom.app (op U) (i.app (op U) (ULift.up x)) = _
  rw [← PicardImage.SourceMap.Construction.picardImageSourceMap_value, ← hx, D.representable.homEquiv_comp]
  exact congrArg ((Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf A).obj.map a.op)
    (D.representable.homEquiv.apply_symm_apply y)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Picard.SourceLocalSurjectivity.Construction
