import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Affine Open Cover -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.AffineOpenCover

noncomputable section

/-! A finite affine open cover retaining its explicit spectrum coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def finiteAffineOpenCover (X : Scheme.{u}) [CompactSpace X] : X.AffineOpenCover where
  I₀ := X.affineCover.finiteSubcover.I₀
  X i := X.affineOpenCover.X (X.affineCover.idx i.val)
  f i := X.affineCover.finiteSubcover.f i
  idx := X.affineCover.finiteSubcover.idx
  covers := X.affineCover.finiteSubcover.covers
  map_prop i := inferInstanceAs (IsOpenImmersion (X.affineCover.finiteSubcover.f i))

instance finiteAffineOpenCover_fintype (X : Scheme.{u}) [CompactSpace X] :
    Fintype (finiteAffineOpenCover X).I₀ :=
  inferInstanceAs (Fintype X.affineCover.finiteSubcover.I₀)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.AffineOpenCover
