import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.PicardSheafValue
import OAI.AlgebraicGeometry.FormalGeometry.Completion.FppfPairLift
import Mathlib.CategoryTheory.Sites.LocallySurjective

/-! # Picard Local Surjectivity -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.PicardLocalSurjectivity.Construction

noncomputable section

/-! An actual fppf map to the original source dual gives a locally
surjective Poincare-family map into its homogeneous Picard sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle

universe u
variable {S : Scheme.{u}} {A B : Over S} [GrpObj A]
  (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (φ : B ⟶ D.abelian)
  (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.poincare) φ)
      (Picard.PoincareBundle.Vertical.ProductParameters.inputLeft B A))
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.poincare) φ)
      (Picard.PoincareBundle.Vertical.ProductParameters.inputRight B A))
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.poincare) φ)
      (Picard.PoincareBundle.Vertical.ProductParameters.outputPoint B A)))
  (hβ : IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom β))

theorem poincareFamily_nativePicard_locallySurjective
    [Flat φ.left] [Surjective φ.left] [LocallyOfFinitePresentation φ.left] :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
      (ProductPicard.SheafMap.Construction.productNativePicardSheafMap (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.poincare) φ) β hβ) := by
  constructor
  intro T y
  let t := D.representable.homEquiv.symm y
  obtain ⟨U, a, x, _z, haf, has, hap, hx, _hz⟩ := FormalGeometry.Completion.FppfPairLift.Construction.fppf_lift_pair φ t t
  have : Flat a.left := haf
  have : Surjective a.left := has
  have : LocallyOfFinitePresentation a.left := hap
  apply (Scheme.fppfTopology.over S).superset_covering _ (FormalGeometry.Completion.FppfSheafSectionDescent.Construction.fppfSingleton_cover a)
  apply (Sieve.generate_le_iff _ _).mpr
  intro V b hb
  cases hb
  refine ⟨ULift.up x, ?_⟩
  rw [PicardSheafValue.Construction.poincareFamily_nativePicard_value, ← hx, D.representable.homEquiv_comp]
  exact congrArg ((Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf A).obj.map a.op)
    (D.representable.homEquiv.apply_symm_apply y)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.PicardLocalSurjectivity.Construction
