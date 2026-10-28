import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IsogenyFrameTransport

/-! # Isogeny Source Frame -/

namespace OAI.RepresentationTheory.Theta.Geometric.IsogenySourceFrame

noncomputable section

/-! Pull a chosen target frame back through the actual rational Tate
isogeny; the resulting preimage lattice is the original target integral image. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IsogenyFrameTransport

variable {R k : Type} [CommRing R] [Field k] [IsAlgClosed k]
    {g N s n q : ℕ} [Fact q.Prime]
    {P Q : AlgebraicGeometry.AbelianScheme.TateComparison.PEL.PELFamilyData R g N (Spec (.of k))}
    (e : AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenies.PELIsogeny P Q n)
    (frame : AlgebraicGeometry.AbelianScheme.TateComparison.Rational.SplitTateFrame s Q.abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q)

def isogenySourceFrame : AlgebraicGeometry.AbelianScheme.TateComparison.Rational.SplitTateFrame s P.abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q :=
  (AlgebraicGeometry.AbelianScheme.TateComparison.GeometricIsogeny.geometricTateIsogenyEquiv (𝟙 (Spec (.of k))) q e.isogeny).trans frame

theorem isogenySourceFrame_equivariant (χ : Fin s × Bool → R →+* ℤ_[q])
    (hf : AlgebraicGeometry.AbelianScheme.TateComparison.Rational.IsSplitActionFrame Q (Over.mk (𝟙 (Spec (.of k)))) q χ frame) :
    AlgebraicGeometry.AbelianScheme.TateComparison.Rational.IsSplitActionFrame P (Over.mk (𝟙 (Spec (.of k)))) q χ (isogenySourceFrame e frame) := by
  intro a z v i
  change frame (AlgebraicGeometry.AbelianScheme.TateComparison.GeometricIsogeny.geometricTateIsogenyEquiv (𝟙 (Spec (.of k))) q e.isogeny
    (AlgebraicGeometry.AbelianScheme.TateComparison.Rational.rationalTateMap (T := Over.mk (𝟙 (Spec (.of k)))) (q := q)
      (AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap P.abelian.scheme (P.action a)) z)) v i = _
  rw [e.rationalTate_action]
  exact hf a _ v i

theorem targetFrame_isogenySourceFrame : e.targetFrame q (isogenySourceFrame e frame) = frame := by
  ext z v i
  change frame (AlgebraicGeometry.AbelianScheme.TateComparison.GeometricIsogeny.geometricTateIsogenyEquiv (𝟙 (Spec (.of k))) q e.isogeny
    ((AlgebraicGeometry.AbelianScheme.TateComparison.GeometricIsogeny.geometricTateIsogenyEquiv (𝟙 (Spec (.of k))) q e.isogeny).symm z)) v i = frame z v i
  rw [LinearEquiv.apply_symm_apply]

theorem isogenySourceFrame_preimage :
    (AlgebraicGeometry.AbelianScheme.TateComparison.Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) e.isogeny.hom).map
      ((isogenySourceFrame e frame).toLinearMap.restrictScalars ℤ_[q]) =
        AlgebraicGeometry.AbelianScheme.TateComparison.Rational.framedIntegralTateImage frame := by
  have H := e.targetFrame_integral q (isogenySourceFrame e frame)
  rw [targetFrame_isogenySourceFrame] at H
  exact H.symm

theorem isogenySourceFrame_complement_lattice
    {A : Over (Spec (.of k))} [GrpObj A] [IsCommMonObj A]
    (f : Q.abelian.scheme ⟶ A) [IsMonHom f] (v : Fin s × Bool) :
    AlgebraicGeometry.AbelianScheme.TateComparison.Rational.framedTateLattice frame f v =
      AlgebraicGeometry.AbelianScheme.TateComparison.Rational.framedTateLattice (isogenySourceFrame e frame) (e.isogeny.hom ≫ f) v := by
  rw [← e.targetFrame_lattice q (isogenySourceFrame e frame) f v, targetFrame_isogenySourceFrame]

end

end OAI.RepresentationTheory.Theta.Geometric.IsogenySourceFrame
