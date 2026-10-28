import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.SheafMap
import Mathlib.CategoryTheory.Sites.LocallyInjective

/-! # Sheaf Kernel -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.SheafKernel.Construction

noncomputable section

/-! Detect the kernel of the actual product-line Picard map by fppf-local
trivializations of its family line, without a representing dual scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers

universe u

variable {S : Scheme.{u}} {B A : Over S} [GrpObj A]
  (R : Picard.PoincareBundle.Line.Bundles.LineBundle (B ⊗ A).left)
  (βv : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Picard.PoincareBundle.Line.Fibers.fiber R (Picard.PoincareBundle.Vertical.ProductParameters.inputLeft B A))
    (Picard.PoincareBundle.Line.Fibers.fiber R (Picard.PoincareBundle.Vertical.ProductParameters.inputRight B A))
    (Picard.PoincareBundle.Line.Fibers.fiber R (Picard.PoincareBundle.Vertical.ProductParameters.outputPoint B A)))
  (hβv : IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom βv))

set_option backward.isDefEq.respectTransparency false in
theorem productNativeHomogeneousClass_eq_one_iff {T : Over S} (x : T ⟶ B) :
    SheafMap.Construction.productNativeHomogeneousClass R βv hβv x = 1 ↔
      Nonempty ((Scheme.Modules.pullback (x ⊗ₘ 𝟙 A).left).obj R.sheaf ≅
        AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (T ⊗ A).left) := by
  constructor
  · intro h
    exact Quotient.exact (congrArg Subtype.val h)
  · intro h
    exact Subtype.ext (Quotient.sound h)

/-- The arrows on which the family line becomes genuinely trivial. -/
def productLineTrivializationSieve {T : Over S} (x : T ⟶ B) : Sieve T :=
  Presheaf.equalizerSieve (F := Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf A)
    (SheafMap.Construction.productNativeHomogeneousClass R βv hβv x) 1

theorem productLineTrivializationSieve_apply {T U : Over S} (x : T ⟶ B) (a : U ⟶ T) :
    productLineTrivializationSieve R βv hβv x a ↔
      Nonempty ((Scheme.Modules.pullback ((a ≫ x) ⊗ₘ 𝟙 A).left).obj R.sheaf ≅
        AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (U ⊗ A).left) := by
  change (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf A).map a.op (SheafMap.Construction.productNativeHomogeneousClass R βv hβv x) =
    (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf A).map a.op 1 ↔ _
  rw [SheafMap.Construction.productNativeHomogeneousClass_natural]
  have h1 := ((Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard.homogeneousPicardGroupPresheaf A).map a.op).hom.map_one
  change (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf A).map a.op 1 = 1 at h1
  rw [h1]
  exact productNativeHomogeneousClass_eq_one_iff R βv hβv (a ≫ x)

variable [GrpObj B]
  (βh : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Picard.PoincareBundle.Line.Fibers.fiber R (Picard.PoincareBundle.Product.ParameterSchemes.inputLeft B A))
    (Picard.PoincareBundle.Line.Fibers.fiber R (Picard.PoincareBundle.Product.ParameterSchemes.inputRight B A))
    (Picard.PoincareBundle.Line.Fibers.fiber R (Picard.PoincareBundle.Product.ParameterSchemes.outputPoint B A)))
  (hβh : IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom βh))

theorem productNativePicardSectionHom_eq_one_iff {T : Over S} (x : T ⟶ B) :
    SheafMap.Construction.productNativePicardSectionHom R βv hβv βh hβh T x = 1 ↔
      productLineTrivializationSieve R βv hβv x ∈ (Scheme.fppfTopology.over S) T := by
  let J := Scheme.fppfTopology.over S
  let unitMap : Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf A ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf A).obj :=
    toSheafify J (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf A)
  have h1 : unitMap.app (op T) 1 = 1 :=
    (Picard.Homomorphisms.GroupSheafification.Construction.picardTypeSheafifyUnitHom (Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard.homogeneousPicardGroupPresheaf A) (op T)).map_one
  change unitMap.app (op T) (SheafMap.Construction.productNativeHomogeneousClass R βv hβv x) = 1 ↔ _
  rw [← h1]
  constructor
  · intro h
    exact Presheaf.equalizerSieve_mem (Scheme.fppfTopology.over S)
      (toSheafify (Scheme.fppfTopology.over S) (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf A)) _ _ h
  · intro h
    apply ((Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf A).property.isSheafFor _ h).isSeparatedFor.ext
    intro U a ha
    rw [← unitMap.naturality_apply, ← unitMap.naturality_apply]
    exact congrArg (unitMap.app (op U)) ha

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.SheafKernel.Construction
