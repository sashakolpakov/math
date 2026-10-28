import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.CechResolution
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-! # Affine Cover -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Finite.AffineCover

noncomputable section

/-! A genuine finite affine open cover of every quasi-compact complex scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [QuasiCompact X.hom]

def finiteAlgebraicAffineCover : X.left.OpenCover := by
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  exact X.left.affineCover.finiteSubcover

instance finiteAlgebraicAffineCover_finite : Fintype (finiteAlgebraicAffineCover X).I₀ := by
  dsimp [finiteAlgebraicAffineCover]
  infer_instance

instance finiteAlgebraicAffineCover_affine (i : (finiteAlgebraicAffineCover X).I₀) :
    IsAffine ((finiteAlgebraicAffineCover X).X i) := by
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  dsimp [finiteAlgebraicAffineCover] at i ⊢
  exact inferInstanceAs (IsAffine (X.left.affineCover.X _))

def finiteAlgebraicAffineOpens : (finiteAlgebraicAffineCover X).I₀ → X.left.Opens :=
  fun i => ((finiteAlgebraicAffineCover X).f i).opensRange

theorem finiteAlgebraicAffineOpens_affine (i : (finiteAlgebraicAffineCover X).I₀) :
    IsAffineOpen (finiteAlgebraicAffineOpens X i) :=
  isAffineOpen_opensRange ((finiteAlgebraicAffineCover X).f i)

theorem finiteAlgebraicAffineOpens_cover : ⨆ i, finiteAlgebraicAffineOpens X i = ⊤ :=
  (finiteAlgebraicAffineCover X).iSup_opensRange

end

end OAI.AlgebraicGeometry.Comparison.Betti.Finite.AffineCover
