import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FieldQuotient.DualPointNaturality
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.Covers
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.Noetherian
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

/-! # Dual Cover -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FieldQuotient.DualCover

noncomputable section

section

/-! Evaluating normalized Poincare comparisons preserves their actual
composition law over the quotient relation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.PullHom Pseudofunctor.LocallyDiscreteOpToCat

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FieldQuotient.DualSheaf.Representation OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.CharacterKernelQuotient

variable {k : Type} [Field k] {d : ℕ}
variable {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of k))} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of k))}
variable (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B A) (r : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)
variable (T : Over (Spec (.of k))) [CompactSpace T.left] [QuasiSeparatedSpace T.left]
variable (x y z : T ⟶ D.abelian.scheme ⊗ B.scheme)
variable (hxy : x ≫ ((NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).projection ▷ B.scheme) =
  y ≫ ((NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).projection ▷ B.scheme))
variable (hyz : y ≫ ((NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).projection ▷ B.scheme) =
  z ≫ ((NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).projection ▷ B.scheme))

abbrev quotientDualPointIso_comp :=
  AbelianScheme.FrobeniusKernel.FamilyPointIsomorphisms.Construction.familyPointIso_comp_of_eq B (DualSheaf.quotientDualSourcePoincare D f) x y
    (AbelianScheme.FrobeniusKernel.FamilyPointIsomorphisms.Construction.familyProjection_fiber_eq (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).projection x y hxy)
    (DualNormalizedTransport.quotientDualNormalizedIso D f r T (x ≫ fst D.abelian.scheme B.scheme)
      (y ≫ fst D.abelian.scheme B.scheme)
      (AbelianScheme.FrobeniusKernel.FamilyPointIsomorphisms.Construction.familyProjection_parameter_eq (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).projection x y hxy))
    z (AbelianScheme.FrobeniusKernel.FamilyPointIsomorphisms.Construction.familyProjection_fiber_eq (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).projection y z hyz)
    (DualNormalizedTransport.quotientDualNormalizedIso D f r T (y ≫ fst D.abelian.scheme B.scheme)
      (z ≫ fst D.abelian.scheme B.scheme)
      (AbelianScheme.FrobeniusKernel.FamilyPointIsomorphisms.Construction.familyProjection_parameter_eq (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).projection y z hyz))
    (DualNormalizedTransport.quotientDualNormalizedIso D f r T (x ≫ fst D.abelian.scheme B.scheme)
      (z ≫ fst D.abelian.scheme B.scheme)
      (AbelianScheme.FrobeniusKernel.FamilyPointIsomorphisms.Construction.familyProjection_parameter_eq (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).projection x z (hxy.trans hyz)))
    (DualNormalizedTransport.quotientDualNormalizedIso_comp D f r T (x ≫ fst D.abelian.scheme B.scheme)
      (y ≫ fst D.abelian.scheme B.scheme)
      (AbelianScheme.FrobeniusKernel.FamilyPointIsomorphisms.Construction.familyProjection_parameter_eq (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).projection x y hxy)
      (z ≫ fst D.abelian.scheme B.scheme)
      (AbelianScheme.FrobeniusKernel.FamilyPointIsomorphisms.Construction.familyProjection_parameter_eq (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).projection y z hyz))

end

/-! The Poincare family cover is an actual finite flat surjective
homomorphism, and the schemes used for its action equations are proper. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

theorem groupHom_whiskerRight {C : Type*} [Category* C] [CartesianMonoidalCategory C] [BraidedCategory C]
    {X Y Z : C} [GrpObj X] [GrpObj Y] [GrpObj Z] (p : X ⟶ Y) [IsMonHom p] :
    IsMonHom (p ▷ Z) := inferInstance

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FieldQuotient.DualSheaf.Representation OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.CharacterKernelQuotient

variable {k : Type} [Field k] {d : ℕ}
variable {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of k))} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of k))}
variable (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B A)

def quotientDualPoincareCover : D.abelian.scheme ⊗ B.scheme ⟶
    (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterAbelian D f).scheme ⊗ B.scheme :=
  (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).projection ▷ B.scheme

instance quotientDualPoincareCover_monHom : IsMonHom (quotientDualPoincareCover D f) := by
  exact @groupHom_whiskerRight (Over (Spec (.of k))) inferInstance inferInstance inferInstance
    D.abelian.scheme (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterAbelian D f).scheme B.scheme
    D.abelian.group (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterAbelian D f).group B.group
    (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).projection (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).groupHom

instance quotientDualPoincareCover_finite : IsFinite (quotientDualPoincareCover D f).left := by
  unfold quotientDualPoincareCover
  rw [← tensorHom_id]
  exact Picard.PoincareBundle.Product.Covers.property_tensor (@IsFinite)
    (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).projection (𝟙 B.scheme) (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).finite
    (inferInstanceAs (IsFinite (𝟙 B.scheme.left)))

instance quotientDualPoincareCover_flat : Flat (quotientDualPoincareCover D f).left := by
  unfold quotientDualPoincareCover
  rw [← tensorHom_id]
  have : Flat (Over.Hom.left (𝟙 B.scheme)) := inferInstanceAs (Flat (𝟙 B.scheme.left))
  exact Picard.PoincareBundle.Product.Covers.tensorFlat (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).projection (𝟙 B.scheme)

instance quotientDualPoincareCover_surjective : Surjective (quotientDualPoincareCover D f).left := by
  unfold quotientDualPoincareCover
  rw [← tensorHom_id]
  have : Surjective (Over.Hom.left (𝟙 B.scheme)) := inferInstanceAs (Surjective (𝟙 B.scheme.left))
  exact Picard.PoincareBundle.Product.Covers.tensorSurjective (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).projection (𝟙 B.scheme)

instance quotientDualPoincareCover_fp : LocallyOfFinitePresentation (quotientDualPoincareCover D f).left := by
  unfold quotientDualPoincareCover
  rw [← tensorHom_id]
  exact Picard.PoincareBundle.Product.Covers.property_tensor (@LocallyOfFinitePresentation)
    (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).projection (𝟙 B.scheme) (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).finitelyPresented
    (inferInstanceAs (LocallyOfFinitePresentation (𝟙 B.scheme.left)))

instance quotientDualPoincareSource_proper : IsProper (D.abelian.scheme ⊗ B.scheme).hom := by
  dsimp
  infer_instance

instance quotientDualPoincareTarget_noetherian :
    IsLocallyNoetherian ((NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterAbelian D f).scheme ⊗ B.scheme).left :=
  Picard.PoincareBundle.Product.Noetherian.product_noetherian (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterAbelian D f).scheme B.scheme

instance quotientDualPoincareKernel_proper : IsProper (Picard.PoincareBundle.Kernel.Scheme.kernelObject (quotientDualPoincareCover D f)).hom := by
  have : IsFinite (Picard.PoincareBundle.Kernel.Scheme.kernelObject (quotientDualPoincareCover D f)).hom := Picard.PoincareBundle.Kernel.Scheme.kernel_isFinite (quotientDualPoincareCover D f)
  infer_instance

instance quotientDualPoincareAction_proper :
    IsProper ((D.abelian.scheme ⊗ B.scheme) ⊗ Picard.PoincareBundle.Kernel.Scheme.kernelObject (quotientDualPoincareCover D f)).hom := by
  dsimp only [Over.tensorObj_hom]
  infer_instance

instance quotientDualPoincareTriple_proper :
    IsProper (((D.abelian.scheme ⊗ B.scheme) ⊗ Picard.PoincareBundle.Kernel.Scheme.kernelObject (quotientDualPoincareCover D f)) ⊗
      Picard.PoincareBundle.Kernel.Scheme.kernelObject (quotientDualPoincareCover D f)).hom := by
  dsimp only [Over.tensorObj_hom]
  infer_instance

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FieldQuotient.DualCover
