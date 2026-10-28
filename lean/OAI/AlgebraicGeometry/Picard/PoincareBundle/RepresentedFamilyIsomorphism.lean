import OAI.AlgebraicGeometry.Picard.PoincareBundle.NormalizedComparison
import OAI.AlgebraicGeometry.Picard.PoincareBundle.HomogeneousSectionEquality
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.FamilyNormalization
import OAI.AlgebraicGeometry.Picard.PoincareBundle.SharedRepresentation
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.Homomorphism

/-! # Represented Family Isomorphism -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.RepresentedFamilyIsomorphism.Family

noncomputable section

/-! The constructed Picard map identifies its original normalized family with the actual universal Poincare family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.Map OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ProductParameters OAI.AlgebraicGeometry.Picard.PoincareBundle.SharedRepresentation OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
  (D : Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A.scheme)
  {T : Over (Spec (.of k))} [CompactSpace T.left] [QuasiSeparatedSpace T.left]
  (R : Line.Bundles.LineBundle (T ⊗ A.scheme).left)
  (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Line.Fibers.fiber R (Vertical.ProductParameters.inputLeft T A.scheme)) (Line.Fibers.fiber R (Vertical.ProductParameters.inputRight T A.scheme))
    (Line.Fibers.fiber R (Vertical.ProductParameters.outputPoint T A.scheme)))
  (hβ : IsIso (Bilinear.BilinearPullback.toHom β))
  (γ : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap
    (Line.Fibers.fiber (Line.Comparison.Bundle.fromShared D.poincare) (Vertical.ProductParameters.inputLeft D.abelian A.scheme))
    (Line.Fibers.fiber (Line.Comparison.Bundle.fromShared D.poincare) (Vertical.ProductParameters.inputRight D.abelian A.scheme))
    (Line.Fibers.fiber (Line.Comparison.Bundle.fromShared D.poincare) (Vertical.ProductParameters.outputPoint D.abelian A.scheme)))
  (hγ : IsIso (Bilinear.BilinearPullback.toHom γ))

include γ hγ in
omit [IsAlgClosed k] [CompactSpace T.left] [QuasiSeparatedSpace T.left] in
/-- The represented map gives equality of the original and universal actual relative Picard sections. -/
theorem relative_class :
    (Functor.toRelativePicard A.scheme).app (op T) (Line.Bundles.LineBundleClass.mk R) =
      (Functor.toRelativePicard A.scheme).app (op T)
        (Line.Bundles.LineBundleClass.mk
          (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared D.poincare) (Product.Map.representedMap R β hβ (SharedRepresentation.representation D)))) := by
  have hm : (SharedRepresentation.representation D).homEquiv (Product.Map.representedMap R β hβ (SharedRepresentation.representation D)) =
      Product.Map.sectionClass R β hβ (𝟙 T) := Equiv.apply_symm_apply _ _
  have hq := Product.Homomorphism.universalSection_action (Line.Comparison.Bundle.fromShared D.poincare) γ hγ
    (SharedRepresentation.representation D) (SharedRepresentation.universalClass D γ hγ) (Product.Map.representedMap R β hβ (SharedRepresentation.representation D))
  have he := HomogeneousSectionEquality.relative_eq A.scheme
    (Product.Map.homogeneousClass R β hβ (𝟙 T))
    (Product.Map.homogeneousClass (Line.Comparison.Bundle.fromShared D.poincare) γ hγ (Product.Map.representedMap R β hβ (SharedRepresentation.representation D)))
    (hm.symm.trans hq)
  change (Functor.toRelativePicard A.scheme).app (op T)
    (Vertical.Homogeneity.familyClass R (𝟙 T)) = _ at he
  rw [FamilyIdentity.Family.familyClass_id] at he
  exact he

variable
  (eR : (Scheme.Modules.pullback (lift (𝟙 T) (1 : T ⟶ A.scheme)).left).obj R.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left)

include γ hγ

/-- The actual family isomorphism is constructed from Picard equality and preserves the original zero frame. -/
theorem normalized_iso :
    ∃ e : R.sheaf ≅ (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared D.poincare)
      (Product.Map.representedMap R β hβ (SharedRepresentation.representation D))).sheaf,
      (Scheme.Modules.pullback (lift (𝟙 T) (1 : T ⟶ A.scheme)).left).map e.hom ≫
        (Poincare.FamilyNormalization.Family.zeroFrame D (Product.Map.representedMap R β hβ (SharedRepresentation.representation D))).hom = eR.hom :=
  NormalizedComparison.normalized_iso_of_picard_eq A R
    (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared D.poincare) (Product.Map.representedMap R β hβ (SharedRepresentation.representation D))) eR
    (Poincare.FamilyNormalization.Family.zeroFrame D (Product.Map.representedMap R β hβ (SharedRepresentation.representation D)))
    (relative_class A D R β hβ γ hγ)

/-- The original zero frame uniquely fixes the actual universal-family identification. -/
theorem existsUnique_normalized_iso :
    ∃! e : R.sheaf ≅ (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared D.poincare)
      (Product.Map.representedMap R β hβ (SharedRepresentation.representation D))).sheaf,
      (Scheme.Modules.pullback (lift (𝟙 T) (1 : T ⟶ A.scheme)).left).map e.hom ≫
        (Poincare.FamilyNormalization.Family.zeroFrame D (Product.Map.representedMap R β hβ (SharedRepresentation.representation D))).hom = eR.hom := by
  obtain ⟨e, he⟩ := normalized_iso A D R β hβ γ hγ eR
  refine ⟨e, he, ?_⟩
  intro d hd
  exact NormalizedComparison.normalized_iso_unique A R
    (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared D.poincare) (Product.Map.representedMap R β hβ (SharedRepresentation.representation D))) eR
    (Poincare.FamilyNormalization.Family.zeroFrame D (Product.Map.representedMap R β hβ (SharedRepresentation.representation D))) d e hd he

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.RepresentedFamilyIsomorphism.Family
