import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientDualTransportNaturality
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FamilyPointIsomorphisms

/-! # Quotient Dual Point Transport -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientDualPointTransport.Construction

noncomputable section

/-! Evaluate normalized family comparisons at actual points of the
abelian factor to obtain line-fiber comparisons over the quotient. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.PullbackFiberComposition

variable {k : Type} [Field k] [IsAlgClosed k] {d h : ℕ}
variable {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of k))} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h (Spec (.of k))}
variable (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B A) (r : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)
variable (T : Over (Spec (.of k))) [CompactSpace T.left] [QuasiSeparatedSpace T.left]
variable (x y : T ⟶ D.abelian.scheme ⊗ B.scheme)
variable (hxy : x ≫ ((CharacterQuotient.Construction.isogenyCharacterQuotient D f).projection ▷ B.scheme) =
  y ≫ ((CharacterQuotient.Construction.isogenyCharacterQuotient D f).projection ▷ B.scheme))

def quotientDualPointIso :
    Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared (QuotientDualSourcePoincare.Construction.quotientDualSourcePoincare D f)) x ≅
      Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared (QuotientDualSourcePoincare.Construction.quotientDualSourcePoincare D f)) y :=
  Picard.PoincareBundle.PullbackFiberComposition.pullIso (Picard.PoincareBundle.Geometric.KernelLinearization.overModulePullbacks (Spec (.of k)))
    (A := D.abelian.scheme ⊗ B.scheme) (B := D.abelian.scheme ⊗ B.scheme)
    (M := (QuotientDualSourcePoincare.Construction.quotientDualSourcePoincare D f).sheaf) (N := (QuotientDualSourcePoincare.Construction.quotientDualSourcePoincare D f).sheaf)
    (x := (x ≫ fst D.abelian.scheme B.scheme) ▷ B.scheme)
    (y := (y ≫ fst D.abelian.scheme B.scheme) ▷ B.scheme)
    (QuotientDualNormalizedTransport.Construction.quotientDualNormalizedIso D f r T (x ≫ fst D.abelian.scheme B.scheme)
      (y ≫ fst D.abelian.scheme B.scheme)
      (FamilyPointIsomorphisms.Construction.familyProjection_parameter_eq (CharacterQuotient.Construction.isogenyCharacterQuotient D f).projection x y hxy))
    (FamilyPointIsomorphisms.Construction.familyPointGraph x) x y (FamilyPointIsomorphisms.Construction.familyPointGraph_factor x x rfl)
    (FamilyPointIsomorphisms.Construction.familyPointGraph_factor x y (FamilyPointIsomorphisms.Construction.familyProjection_fiber_eq (CharacterQuotient.Construction.isogenyCharacterQuotient D f).projection x y hxy))

theorem quotientDualPointIso_self : quotientDualPointIso D f r T x x rfl = Iso.refl _ := by
  have hn := QuotientDualNormalizedTransport.Construction.quotientDualNormalizedIso_self D f r T (x ≫ fst D.abelian.scheme B.scheme)
  have hp := congrArg (fun e => Picard.PoincareBundle.PullbackFiberComposition.pullIso (Picard.PoincareBundle.Geometric.KernelLinearization.overModulePullbacks (Spec (.of k)))
    (A := D.abelian.scheme ⊗ B.scheme) (B := D.abelian.scheme ⊗ B.scheme)
    (M := (QuotientDualSourcePoincare.Construction.quotientDualSourcePoincare D f).sheaf) (N := (QuotientDualSourcePoincare.Construction.quotientDualSourcePoincare D f).sheaf)
    (x := (x ≫ fst D.abelian.scheme B.scheme) ▷ B.scheme)
    (y := (x ≫ fst D.abelian.scheme B.scheme) ▷ B.scheme)
    e (FamilyPointIsomorphisms.Construction.familyPointGraph x) x x (FamilyPointIsomorphisms.Construction.familyPointGraph_factor x x rfl) (FamilyPointIsomorphisms.Construction.familyPointGraph_factor x x rfl)) hn
  exact hp.trans (PullIsoLaws.Construction.pullIso_refl (Picard.PoincareBundle.Geometric.KernelLinearization.overModulePullbacks (Spec (.of k)))
    (A := D.abelian.scheme ⊗ B.scheme) (L := (QuotientDualSourcePoincare.Construction.quotientDualSourcePoincare D f).sheaf)
    (x := (x ≫ fst D.abelian.scheme B.scheme) ▷ B.scheme)
    (FamilyPointIsomorphisms.Construction.familyPointGraph x) x (FamilyPointIsomorphisms.Construction.familyPointGraph_factor x x rfl))

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientDualPointTransport.Construction
