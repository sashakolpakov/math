import OAI.RepresentationTheory.Theta.Geometric.IsogenySourceFrame
import OAI.RepresentationTheory.Theta.Geometric.MarkedPELComplement
import OAI.RepresentationTheory.Theta.Geometric.PowerTatePreimages

/-! # Complement Tate Lattices -/

namespace OAI.RepresentationTheory.Theta.Geometric.ComplementTateLattices

noncomputable section

/-! In target coordinates, the complementary isogeny preimage is the
inverse-multiplier multiple of the transported original source lattice. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj Pointwise

variable {R k : Type} [CommRing R] [Field k] [CharZero k] [IsAlgClosed k]
    {g N s q m : ℕ} [Fact q.Prime]
    {P Q : AlgebraicGeometry.AbelianScheme.TateComparison.PEL.PELFamilyData R g N (Spec (.of k))}
    (e : AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenies.PELIsogeny P Q (q ^ m))
    (frame : AlgebraicGeometry.AbelianScheme.TateComparison.Rational.SplitTateFrame s Q.abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q)

omit [CharZero k] in
theorem isogenySourceFrame_lattice (v : Fin s × Bool) :
    AlgebraicGeometry.AbelianScheme.TateComparison.Rational.framedTateLattice (IsogenySourceFrame.isogenySourceFrame e frame) e.isogeny.hom v = PowerTatePreimages.framedSourceIntegral frame v := by
  rw [AlgebraicGeometry.AbelianScheme.TateComparison.Rational.framedTateLattice, IsogenySourceFrame.isogenySourceFrame_preimage]
  rfl

variable (δ : Fin g → ℕ) (hP : P.polarizationMap.HasPolarizationType δ)
    (hQ : Q.polarizationMap.HasPolarizationType δ) (hq : Nat.Coprime q (∏ i, δ i))

theorem complementary_framedLattice (v : Fin s × Bool) :
    AlgebraicGeometry.AbelianScheme.TateComparison.Rational.framedTateLattice frame (e.multiplierComplement δ hP hQ hq).hom v =
      (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ m)⁻¹ • PowerTatePreimages.framedSourceIntegral (IsogenySourceFrame.isogenySourceFrame e frame) v := by
  rw [IsogenySourceFrame.isogenySourceFrame_complement_lattice e frame]
  rw [PowerTatePreimages.framedTateLattice_congr (IsogenySourceFrame.isogenySourceFrame e frame) _ _
    (PELComplementCompatibility.isogeny_comp_complement e δ hP hQ hq) v]
  exact PowerTatePreimages.powerMultiplication_framedLattice (IsogenySourceFrame.isogenySourceFrame e frame) m v

theorem markedPELComplement_framedLattice (hqN : Nat.Coprime q N) (v : Fin s × Bool) :
    AlgebraicGeometry.AbelianScheme.TateComparison.Rational.framedTateLattice frame (MarkedPELComplement.markedPELComplement e δ hP hQ hq hqN).isogeny.hom v =
      (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ m)⁻¹ • PowerTatePreimages.framedSourceIntegral (IsogenySourceFrame.isogenySourceFrame e frame) v :=
  complementary_framedLattice e frame δ hP hQ hq v

end

end OAI.RepresentationTheory.Theta.Geometric.ComplementTateLattices
