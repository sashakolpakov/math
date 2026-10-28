import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FieldQuotient.DualTransportNaturality
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FamilyPointIsomorphisms

/-! # Dual Point Transport -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FieldQuotient.DualPointTransport

noncomputable section

/-! Evaluate normalized family comparisons at actual points of the
abelian factor to obtain line-fiber comparisons over the quotient. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.PullbackFiberComposition

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FieldQuotient.DualSheaf.Representation OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.CharacterKernelQuotient

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FamilyPointIsomorphisms.Construction
  (familyProjection_parameter_eq familyProjection_fiber_eq familyPointGraph familyPointGraph_factor)

variable {k : Type} [Field k] {d : ℕ}
variable {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of k))} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of k))}
variable (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B A) (r : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)
variable (T : Over (Spec (.of k))) [CompactSpace T.left] [QuasiSeparatedSpace T.left]
variable (x y : T ⟶ D.abelian.scheme ⊗ B.scheme)
variable (hxy : x ≫ ((NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).projection ▷ B.scheme) =
  y ≫ ((NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).projection ▷ B.scheme))

def quotientDualPointIso :
    Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared (DualSheaf.quotientDualSourcePoincare D f)) x ≅
      Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared (DualSheaf.quotientDualSourcePoincare D f)) y :=
  Picard.PoincareBundle.PullbackFiberComposition.pullIso (Picard.PoincareBundle.Geometric.KernelLinearization.overModulePullbacks (Spec (.of k)))
    (A := D.abelian.scheme ⊗ B.scheme) (B := D.abelian.scheme ⊗ B.scheme)
    (M := (DualSheaf.quotientDualSourcePoincare D f).sheaf) (N := (DualSheaf.quotientDualSourcePoincare D f).sheaf)
    (x := (x ≫ fst D.abelian.scheme B.scheme) ▷ B.scheme)
    (y := (y ≫ fst D.abelian.scheme B.scheme) ▷ B.scheme)
    (DualNormalizedTransport.quotientDualNormalizedIso D f r T (x ≫ fst D.abelian.scheme B.scheme)
      (y ≫ fst D.abelian.scheme B.scheme)
      (AbelianScheme.FrobeniusKernel.FamilyPointIsomorphisms.Construction.familyProjection_parameter_eq (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).projection x y hxy))
    (AbelianScheme.FrobeniusKernel.FamilyPointIsomorphisms.Construction.familyPointGraph x) x y (AbelianScheme.FrobeniusKernel.FamilyPointIsomorphisms.Construction.familyPointGraph_factor x x rfl)
    (AbelianScheme.FrobeniusKernel.FamilyPointIsomorphisms.Construction.familyPointGraph_factor x y (AbelianScheme.FrobeniusKernel.FamilyPointIsomorphisms.Construction.familyProjection_fiber_eq (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).projection x y hxy))

theorem quotientDualPointIso_self : quotientDualPointIso D f r T x x rfl = Iso.refl _ := by
  have hn := DualNormalizedTransport.quotientDualNormalizedIso_self D f r T (x ≫ fst D.abelian.scheme B.scheme)
  have hp := congrArg (fun e => Picard.PoincareBundle.PullbackFiberComposition.pullIso (Picard.PoincareBundle.Geometric.KernelLinearization.overModulePullbacks (Spec (.of k)))
    (A := D.abelian.scheme ⊗ B.scheme) (B := D.abelian.scheme ⊗ B.scheme)
    (M := (DualSheaf.quotientDualSourcePoincare D f).sheaf) (N := (DualSheaf.quotientDualSourcePoincare D f).sheaf)
    (x := (x ≫ fst D.abelian.scheme B.scheme) ▷ B.scheme)
    (y := (x ≫ fst D.abelian.scheme B.scheme) ▷ B.scheme)
    e (AbelianScheme.FrobeniusKernel.FamilyPointIsomorphisms.Construction.familyPointGraph x) x x (AbelianScheme.FrobeniusKernel.FamilyPointIsomorphisms.Construction.familyPointGraph_factor x x rfl) (AbelianScheme.FrobeniusKernel.FamilyPointIsomorphisms.Construction.familyPointGraph_factor x x rfl)) hn
  exact hp.trans (AbelianScheme.FrobeniusKernel.PullIsoLaws.Construction.pullIso_refl (Picard.PoincareBundle.Geometric.KernelLinearization.overModulePullbacks (Spec (.of k)))
    (A := D.abelian.scheme ⊗ B.scheme) (L := (DualSheaf.quotientDualSourcePoincare D f).sheaf)
    (x := (x ≫ fst D.abelian.scheme B.scheme) ▷ B.scheme)
    (AbelianScheme.FrobeniusKernel.FamilyPointIsomorphisms.Construction.familyPointGraph x) x (AbelianScheme.FrobeniusKernel.FamilyPointIsomorphisms.Construction.familyPointGraph_factor x x rfl))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FieldQuotient.DualPointTransport
