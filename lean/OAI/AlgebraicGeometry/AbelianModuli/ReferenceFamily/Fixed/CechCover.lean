import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.AffineCoverIntersections
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TangentBasePoint

/-! # Cech Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Fixed.CechCover

noncomputable section

/-! Every affine cover of the original family gives its actual
inverse-image cover of the fixed fiber, with the original pair and
triple intersections retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (k R : Type) [Field k] [CommRing R] [Algebra R k]
    (X : Over (Spec (.of R))) (U : X.left.AffineOpenCover)

def fixedFamilyCechCover (i : U.I₀) : (TangentBasePoint.fixedFamilyFiber k R X).left.Opens :=
  FixedFiber.CoordinateProjection.fixedFiberAffineOpen R k X (Family.AffineCoverIntersections.familyCoverAffineOpen R X U i)

theorem fixedFamilyCechCover_covers : iSup (fixedFamilyCechCover k R X U) = ⊤ := by
  apply top_unique
  intro x _
  apply Opens.mem_iSup.mpr
  refine ⟨U.idx (FixedFiber.CoordinateProjection.fixedFamilyProjection R k X x), ?_⟩
  exact U.covers (FixedFiber.CoordinateProjection.fixedFamilyProjection R k X x)

variable [IsSeparated X.hom]

theorem fixedFamilyCechCover_pair (i j : U.I₀) :
    FixedFiber.CoordinateProjection.fixedFiberAffineOpen R k X (Family.AffineCoverIntersections.familyCoverPairAffineOpen R X U i j) =
      fixedFamilyCechCover k R X U i ⊓ fixedFamilyCechCover k R X U j := rfl

theorem fixedFamilyCechCover_triple (i j l : U.I₀) :
    FixedFiber.CoordinateProjection.fixedFiberAffineOpen R k X (Family.AffineCoverIntersections.familyCoverTripleAffineOpen R X U i j l) =
      (fixedFamilyCechCover k R X U i ⊓ fixedFamilyCechCover k R X U j) ⊓ fixedFamilyCechCover k R X U l := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Fixed.CechCover
