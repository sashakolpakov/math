import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-! # Affine Cover -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.AffineCover.FiniteAffineCover

noncomputable section

/-! A genuine finite affine open cover of every quasi-compact scheme over an affine base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R))) [QuasiCompact X.hom]

def finiteAlgebraicAffineCover : X.left.OpenCover := by
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  exact X.left.affineCover.finiteSubcover

instance finiteAlgebraicAffineCover_finite : Fintype (finiteAlgebraicAffineCover R X).I₀ := by
  dsimp [finiteAlgebraicAffineCover]
  infer_instance

instance finiteAlgebraicAffineCover_affine (i : (finiteAlgebraicAffineCover R X).I₀) :
    IsAffine ((finiteAlgebraicAffineCover R X).X i) := by
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  dsimp [finiteAlgebraicAffineCover] at i ⊢
  exact inferInstanceAs (IsAffine (X.left.affineCover.X _))

def finiteAlgebraicAffineOpens : (finiteAlgebraicAffineCover R X).I₀ → X.left.Opens :=
  fun i => ((finiteAlgebraicAffineCover R X).f i).opensRange

theorem finiteAlgebraicAffineOpens_affine (i : (finiteAlgebraicAffineCover R X).I₀) :
    IsAffineOpen (finiteAlgebraicAffineOpens R X i) :=
  isAffineOpen_opensRange ((finiteAlgebraicAffineCover R X).f i)

theorem finiteAlgebraicAffineOpens_cover : ⨆ i, finiteAlgebraicAffineOpens R X i = ⊤ :=
  (finiteAlgebraicAffineCover R X).iSup_opensRange

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.AffineCover.FiniteAffineCover
