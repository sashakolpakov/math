import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FieldQuotient.DualPointTransport

/-! # Dual Point Naturality -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FieldQuotient.DualPointNaturality

noncomputable section

/-! The actual quotient-dual fiber comparisons commute with change
of quasi-compact, quasi-separated test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.PullbackFiberComposition OAI.AlgebraicGeometry.Picard.PoincareBundle.PullHom
open Pseudofunctor.LocallyDiscreteOpToCat

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FieldQuotient.DualSheaf.Representation OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.CharacterKernelQuotient

variable {k : Type} [Field k] {d : ℕ}
variable {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of k))} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of k))}
variable (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B A) (r : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)
variable {T U : Over (Spec (.of k))}
variable [CompactSpace T.left] [QuasiSeparatedSpace T.left] [CompactSpace U.left] [QuasiSeparatedSpace U.left]
variable (x y : T ⟶ D.abelian.scheme ⊗ B.scheme)
variable (hxy : x ≫ ((NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).projection ▷ B.scheme) =
  y ≫ ((NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).projection ▷ B.scheme))

abbrev quotientDualPointIso_pullback (t : U ⟶ T)
    (x' y' : U ⟶ D.abelian.scheme ⊗ B.scheme) (hx : t ≫ x = x') (hy : t ≫ y = y')
    (hxy' : x' ≫ ((NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).projection ▷ B.scheme) =
      y' ≫ ((NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).projection ▷ B.scheme)) :=
  AbelianScheme.FrobeniusKernel.FamilyPointIsomorphisms.Construction.familyPointIso_natural B (DualSheaf.quotientDualSourcePoincare D f) x y
    (AbelianScheme.FrobeniusKernel.FamilyPointIsomorphisms.Construction.familyProjection_fiber_eq (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).projection x y hxy)
    (DualNormalizedTransport.quotientDualNormalizedIso D f r T (x ≫ fst D.abelian.scheme B.scheme)
      (y ≫ fst D.abelian.scheme B.scheme)
      (AbelianScheme.FrobeniusKernel.FamilyPointIsomorphisms.Construction.familyProjection_parameter_eq (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).projection x y hxy))
    t x' y' hx hy (AbelianScheme.FrobeniusKernel.FamilyPointIsomorphisms.Construction.familyProjection_fiber_eq (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).projection x' y' hxy')
    (DualNormalizedTransport.quotientDualNormalizedIso D f r U (x' ≫ fst D.abelian.scheme B.scheme)
      (y' ≫ fst D.abelian.scheme B.scheme)
      (AbelianScheme.FrobeniusKernel.FamilyPointIsomorphisms.Construction.familyProjection_parameter_eq (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).projection x' y' hxy'))
    (DualTransportNaturality.quotientDualNormalizedIso_pullback D f r
      (x ≫ fst D.abelian.scheme B.scheme) (y ≫ fst D.abelian.scheme B.scheme)
      (AbelianScheme.FrobeniusKernel.FamilyPointIsomorphisms.Construction.familyProjection_parameter_eq (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).projection x y hxy)
      t (x' ≫ fst D.abelian.scheme B.scheme) (y' ≫ fst D.abelian.scheme B.scheme)
      ((Category.assoc _ _ _).symm.trans (congrArg (fun m => m ≫ fst D.abelian.scheme B.scheme) hx))
      ((Category.assoc _ _ _).symm.trans (congrArg (fun m => m ≫ fst D.abelian.scheme B.scheme) hy))
      (AbelianScheme.FrobeniusKernel.FamilyPointIsomorphisms.Construction.familyProjection_parameter_eq (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).projection x' y' hxy'))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FieldQuotient.DualPointNaturality
