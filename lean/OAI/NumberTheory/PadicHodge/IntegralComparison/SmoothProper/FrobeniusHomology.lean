import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.FrobeniusCoherence
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CoherentHomology

/-! # Frobenius Homology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.FrobeniusHomology

noncomputable section

/-! The original global Frobenius de Rham cohomology sheaves are coherent. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (k : Type u) [Field k] [Fintype k]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]

def cohomology (n : ℕ) : X.left.Modules := (Frobenius.DeRhamGlobal.complex k X).homology n

theorem quasicoherent (n : ℕ) : (cohomology k X n).IsQuasicoherent := by
  exact @IntegralComparison.Module.CoherentHomology.quasicoherent X.left ((Frobenius.DeRhamGlobal.complex k X).sc n)
    (FrobeniusCoherence.quasicoherent k X ((ComplexShape.up ℕ).prev n))
    (FrobeniusCoherence.quasicoherent k X n)
    (FrobeniusCoherence.quasicoherent k X ((ComplexShape.up ℕ).next n))

theorem finiteType (n : ℕ) : (cohomology k X n).IsFiniteType := by
  exact @IntegralComparison.Module.CoherentHomology.finiteType X.left ((Frobenius.DeRhamGlobal.complex k X).sc n)
    (FrobeniusCoherence.quasicoherent k X ((ComplexShape.up ℕ).prev n))
    (FrobeniusCoherence.quasicoherent k X n)
    (FrobeniusCoherence.quasicoherent k X ((ComplexShape.up ℕ).next n))
    (LocallyOfFiniteType.isLocallyNoetherian X.hom) (FrobeniusCoherence.finiteType k X n)

theorem sheaf_cohomology_finite (hprojective : Projectivity.Construction.ProjectiveOver k X.hom) (n q : ℕ) :
    letI := Projective.CoherentFiniteness.coefficientModule k X.hom (cohomology k X n) q
    Module.Finite k (AlgebraicGeometry.SheafCohomology.AffineH.Projective.H (cohomology k X n) q) := by
  let : (cohomology k X n).IsQuasicoherent := quasicoherent k X n
  let : (cohomology k X n).IsFiniteType := finiteType k X n
  exact Projective.CoherentFiniteness.cohomology_finite k X.hom hprojective (cohomology k X n) q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.FrobeniusHomology
