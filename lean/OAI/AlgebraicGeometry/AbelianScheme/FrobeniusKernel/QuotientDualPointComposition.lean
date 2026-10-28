import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientDualPointNaturality

/-! # Quotient Dual Point Composition -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientDualPointComposition.Construction

noncomputable section

/-! Evaluating normalized Poincare comparisons preserves their actual
composition law over the quotient relation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.PullHom Pseudofunctor.LocallyDiscreteOpToCat

variable {k : Type} [Field k] [IsAlgClosed k] {d h : ℕ}
variable {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of k))} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h (Spec (.of k))}
variable (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B A) (r : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)
variable (T : Over (Spec (.of k))) [CompactSpace T.left] [QuasiSeparatedSpace T.left]
variable (x y z : T ⟶ D.abelian.scheme ⊗ B.scheme)
variable (hxy : x ≫ ((CharacterQuotient.Construction.isogenyCharacterQuotient D f).projection ▷ B.scheme) =
  y ≫ ((CharacterQuotient.Construction.isogenyCharacterQuotient D f).projection ▷ B.scheme))
variable (hyz : y ≫ ((CharacterQuotient.Construction.isogenyCharacterQuotient D f).projection ▷ B.scheme) =
  z ≫ ((CharacterQuotient.Construction.isogenyCharacterQuotient D f).projection ▷ B.scheme))

abbrev quotientDualPointIso_comp :=
  FamilyPointIsomorphisms.Construction.familyPointIso_comp_of_eq B (QuotientDualSourcePoincare.Construction.quotientDualSourcePoincare D f) x y
    (FamilyPointIsomorphisms.Construction.familyProjection_fiber_eq (CharacterQuotient.Construction.isogenyCharacterQuotient D f).projection x y hxy)
    (QuotientDualNormalizedTransport.Construction.quotientDualNormalizedIso D f r T (x ≫ fst D.abelian.scheme B.scheme)
      (y ≫ fst D.abelian.scheme B.scheme)
      (FamilyPointIsomorphisms.Construction.familyProjection_parameter_eq (CharacterQuotient.Construction.isogenyCharacterQuotient D f).projection x y hxy))
    z (FamilyPointIsomorphisms.Construction.familyProjection_fiber_eq (CharacterQuotient.Construction.isogenyCharacterQuotient D f).projection y z hyz)
    (QuotientDualNormalizedTransport.Construction.quotientDualNormalizedIso D f r T (y ≫ fst D.abelian.scheme B.scheme)
      (z ≫ fst D.abelian.scheme B.scheme)
      (FamilyPointIsomorphisms.Construction.familyProjection_parameter_eq (CharacterQuotient.Construction.isogenyCharacterQuotient D f).projection y z hyz))
    (QuotientDualNormalizedTransport.Construction.quotientDualNormalizedIso D f r T (x ≫ fst D.abelian.scheme B.scheme)
      (z ≫ fst D.abelian.scheme B.scheme)
      (FamilyPointIsomorphisms.Construction.familyProjection_parameter_eq (CharacterQuotient.Construction.isogenyCharacterQuotient D f).projection x z (hxy.trans hyz)))
    (QuotientDualNormalizedTransport.Construction.quotientDualNormalizedIso_comp D f r T (x ≫ fst D.abelian.scheme B.scheme)
      (y ≫ fst D.abelian.scheme B.scheme)
      (FamilyPointIsomorphisms.Construction.familyProjection_parameter_eq (CharacterQuotient.Construction.isogenyCharacterQuotient D f).projection x y hxy)
      (z ≫ fst D.abelian.scheme B.scheme)
      (FamilyPointIsomorphisms.Construction.familyProjection_parameter_eq (CharacterQuotient.Construction.isogenyCharacterQuotient D f).projection y z hyz))

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientDualPointComposition.Construction
