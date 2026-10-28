import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.OpenDiagram
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Affine Cover Intersections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.AffineCoverIntersections

noncomputable section

/-! A separated family over an affine base has actual affine pair
and triple intersections of every affine open cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] (X : Over (Spec (.of R)))
    (U : X.left.AffineOpenCover)

def familyCoverAffineOpen (i : U.I₀) : X.left.affineOpens :=
  ⟨(U.f i).opensRange, isAffineOpen_opensRange (U.f i)⟩

variable [IsSeparated X.hom]

theorem family_affineDiagonal : IsAffineHom (pullback.diagonal (terminal.from X.left)) := by
  have : IsSeparated (terminal.from (Spec (.of R))) := inferInstance
  have h : IsSeparated (X.hom ≫ terminal.from (Spec (.of R))) := inferInstance
  have he : X.hom ≫ terminal.from (Spec (.of R)) = terminal.from X.left := Subsingleton.elim _ _
  have : IsSeparated (terminal.from X.left) := he ▸ h
  infer_instance

theorem family_affineIntersection (V W : X.left.Opens)
    (hV : IsAffineOpen V) (hW : IsAffineOpen W) : IsAffineOpen (V ⊓ W) := by
  have := family_affineDiagonal R X
  exact hV.inf hW

def familyCoverPairAffineOpen (i j : U.I₀) : X.left.affineOpens :=
  ⟨(U.f i).opensRange ⊓ (U.f j).opensRange,
    family_affineIntersection R X _ _ (isAffineOpen_opensRange (U.f i)) (isAffineOpen_opensRange (U.f j))⟩

def familyCoverTripleAffineOpen (i j l : U.I₀) : X.left.affineOpens :=
  ⟨(familyCoverPairAffineOpen R X U i j).1 ⊓ (U.f l).opensRange,
    family_affineIntersection R X _ _ (familyCoverPairAffineOpen R X U i j).2
      (isAffineOpen_opensRange (U.f l))⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.AffineCoverIntersections
