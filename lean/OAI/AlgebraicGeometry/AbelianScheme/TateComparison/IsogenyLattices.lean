import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricIsogeny
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.LatticeTransport
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Lattices

/-! # Isogeny Lattices -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IsogenyLattices

noncomputable section

/-! Fullness of the intrinsic lattice of an actual isogeny follows from
the target integral lattice and the proved rational Tate isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

universe u
variable {S : Scheme.{u}} {g h : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S}
  {k : Type u} [Field k] [IsAlgClosed k] (b : Spec (.of k) ⟶ S)
  (q : ℕ) [Fact q.Prime]

theorem isogenyTatePreimage_isLattice (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)
    [Submodule.IsLattice ℚ_[q] (Rational.integralTateImage B.scheme (Over.mk b) q)] :
    Submodule.IsLattice ℚ_[q] (Rational.isogenyTatePreimage (T := Over.mk b) (q := q) f.hom) :=
  LatticeTransport.isLattice_comap_equiv (Rational.integralTateImage B.scheme (Over.mk b) q)
    (GeometricIsogeny.geometricTateIsogenyEquiv b q f)

theorem framedTateLattice_isLattice {s : ℕ}
    (e : Rational.SplitTateFrame s A.scheme (Over.mk b) q) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)
    [Submodule.IsLattice ℚ_[q] (Rational.integralTateImage B.scheme (Over.mk b) q)]
    (v : Fin s × Bool) : Submodule.IsLattice ℚ_[q] (Rational.framedTateLattice e f.hom v) := by
  have := isogenyTatePreimage_isLattice b q f
  have := LatticeTransport.isLattice_map_surjective (Rational.isogenyTatePreimage (T := Over.mk b) (q := q) f.hom)
    e.toLinearMap e.surjective
  apply LatticeTransport.isLattice_map_surjective
  intro z
  exact ⟨fun _ => z, rfl⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IsogenyLattices
