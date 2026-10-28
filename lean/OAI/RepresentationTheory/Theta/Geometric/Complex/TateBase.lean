import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SplitFrameTransport
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Cohomology

/-! # Tate Base -/

namespace OAI.RepresentationTheory.Theta.Geometric.Complex.TateBase

noncomputable section

section

/-! Normalize the two definitionally equal descriptions of the complex
base while the actual family is abstract. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SplitFrameTransport

variable {s q : ℕ} [Fact q.Prime]
    {A : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [GrpObj A] [IsCommMonObj A]

def complexTateFrame_base
    (e : AlgebraicGeometry.AbelianScheme.TateComparison.Rational.SplitTateFrame s A (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) q) :
    AlgebraicGeometry.AbelianScheme.TateComparison.Rational.SplitTateFrame (S := Spec (@CommRingCat.of ℂ (@Field.toCommRing ℂ Complex.instField))) s A
      (Over.mk (𝟙 (Spec (@CommRingCat.of ℂ (@Field.toCommRing ℂ Complex.instField))))) q := by
  simpa only [AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase] using e

theorem complexTateFrame_base_integral
    (e : AlgebraicGeometry.AbelianScheme.TateComparison.Rational.SplitTateFrame s A (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) q) :
    AlgebraicGeometry.AbelianScheme.TateComparison.Rational.framedIntegralTateImage (complexTateFrame_base e) = AlgebraicGeometry.AbelianScheme.TateComparison.Rational.framedIntegralTateImage e := rfl

variable {R : Type} [CommRing R] {g N : ℕ}
    {F : AlgebraicGeometry.AbelianScheme.TateComparison.PEL.PELFamilyData R g N AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}

theorem complexTateFrame_base_equivariant
    (χ : Fin s × Bool → R →+* ℤ_[q])
    (e : AlgebraicGeometry.AbelianScheme.TateComparison.Rational.SplitTateFrame s F.abelian.scheme (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) q)
    (he : AlgebraicGeometry.AbelianScheme.TateComparison.Rational.IsSplitActionFrame F (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) q χ e) :
    AlgebraicGeometry.AbelianScheme.TateComparison.Rational.IsSplitActionFrame (S := Spec (@CommRingCat.of ℂ (@Field.toCommRing ℂ Complex.instField))) F (Over.mk (𝟙 (Spec (@CommRingCat.of ℂ (@Field.toCommRing ℂ Complex.instField))))) q χ
      (complexTateFrame_base e) := he

end

/-! The complex-base notation conversion preserves the actual isogeny
preimage lattices in the same frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SplitFrameTransport

variable {s q : ℕ} [Fact q.Prime]
    {A B : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [GrpObj A] [IsCommMonObj A]
    [GrpObj B] [IsCommMonObj B]

theorem complexTateFrame_base_lattice
    (e : AlgebraicGeometry.AbelianScheme.TateComparison.Rational.SplitTateFrame s A (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) q)
    (f : A ⟶ B) [IsMonHom f] (v : Fin s × Bool) :
    AlgebraicGeometry.AbelianScheme.TateComparison.Rational.framedTateLattice (complexTateFrame_base e) f v = AlgebraicGeometry.AbelianScheme.TateComparison.Rational.framedTateLattice e f v := by
  rfl

end

end OAI.RepresentationTheory.Theta.Geometric.Complex.TateBase
