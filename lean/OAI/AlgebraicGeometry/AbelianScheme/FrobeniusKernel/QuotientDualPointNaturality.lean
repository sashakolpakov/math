import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientDualPointTransport

/-! # Quotient Dual Point Naturality -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientDualPointNaturality.Construction

noncomputable section

/-! The actual quotient-dual fiber comparisons commute with change
of quasi-compact, quasi-separated test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.PullbackFiberComposition OAI.AlgebraicGeometry.Picard.PoincareBundle.PullHom
open Pseudofunctor.LocallyDiscreteOpToCat

variable {k : Type} [Field k] [IsAlgClosed k] {d h : ℕ}
variable {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of k))} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h (Spec (.of k))}
variable (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B A) (r : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)
variable {T U : Over (Spec (.of k))}
variable [CompactSpace T.left] [QuasiSeparatedSpace T.left] [CompactSpace U.left] [QuasiSeparatedSpace U.left]
variable (x y : T ⟶ D.abelian.scheme ⊗ B.scheme)
variable (hxy : x ≫ ((CharacterQuotient.Construction.isogenyCharacterQuotient D f).projection ▷ B.scheme) =
  y ≫ ((CharacterQuotient.Construction.isogenyCharacterQuotient D f).projection ▷ B.scheme))

abbrev quotientDualPointIso_pullback (t : U ⟶ T)
    (x' y' : U ⟶ D.abelian.scheme ⊗ B.scheme) (hx : t ≫ x = x') (hy : t ≫ y = y')
    (hxy' : x' ≫ ((CharacterQuotient.Construction.isogenyCharacterQuotient D f).projection ▷ B.scheme) =
      y' ≫ ((CharacterQuotient.Construction.isogenyCharacterQuotient D f).projection ▷ B.scheme)) :=
  FamilyPointIsomorphisms.Construction.familyPointIso_natural B (QuotientDualSourcePoincare.Construction.quotientDualSourcePoincare D f) x y
    (FamilyPointIsomorphisms.Construction.familyProjection_fiber_eq (CharacterQuotient.Construction.isogenyCharacterQuotient D f).projection x y hxy)
    (QuotientDualNormalizedTransport.Construction.quotientDualNormalizedIso D f r T (x ≫ fst D.abelian.scheme B.scheme)
      (y ≫ fst D.abelian.scheme B.scheme)
      (FamilyPointIsomorphisms.Construction.familyProjection_parameter_eq (CharacterQuotient.Construction.isogenyCharacterQuotient D f).projection x y hxy))
    t x' y' hx hy (FamilyPointIsomorphisms.Construction.familyProjection_fiber_eq (CharacterQuotient.Construction.isogenyCharacterQuotient D f).projection x' y' hxy')
    (QuotientDualNormalizedTransport.Construction.quotientDualNormalizedIso D f r U (x' ≫ fst D.abelian.scheme B.scheme)
      (y' ≫ fst D.abelian.scheme B.scheme)
      (FamilyPointIsomorphisms.Construction.familyProjection_parameter_eq (CharacterQuotient.Construction.isogenyCharacterQuotient D f).projection x' y' hxy'))
    (QuotientDualTransportNaturality.Construction.quotientDualNormalizedIso_pullback D f r
      (x ≫ fst D.abelian.scheme B.scheme) (y ≫ fst D.abelian.scheme B.scheme)
      (FamilyPointIsomorphisms.Construction.familyProjection_parameter_eq (CharacterQuotient.Construction.isogenyCharacterQuotient D f).projection x y hxy)
      t (x' ≫ fst D.abelian.scheme B.scheme) (y' ≫ fst D.abelian.scheme B.scheme)
      ((Category.assoc _ _ _).symm.trans (congrArg (fun m => m ≫ fst D.abelian.scheme B.scheme) hx))
      ((Category.assoc _ _ _).symm.trans (congrArg (fun m => m ≫ fst D.abelian.scheme B.scheme) hy))
      (FamilyPointIsomorphisms.Construction.familyProjection_parameter_eq (CharacterQuotient.Construction.isogenyCharacterQuotient D f).projection x' y' hxy'))

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientDualPointNaturality.Construction
