import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELPicardDualMaps
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BaseChange
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.DualFamilyMorphism
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Quotient
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PolarizedComposites

/-! # PEL Multiplication Dual -/

namespace OAI.RepresentationTheory.Theta.Geometric.PELMultiplicationDual

noncomputable section

/-! The original Rosati condition determines scalar Picard duality on
actual PEL families; no separate multiplication-duality hypothesis is used. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u
variable {S : Scheme.{u}}

theorem pelEndSchemeMap_natCast (A : Over S) [GrpObj A] [IsCommMonObj A] (n : ℕ) :
    AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap A (n : AlgebraicGeometry.AbelianScheme.TateComparison.End.IntegralEnd A) = (𝟙 A) ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, AlgebraicGeometry.AbelianScheme.TateComparison.BaseChange.endSchemeMap_zero, pow_zero]
  | succ n ih => rw [Nat.cast_succ, AlgebraicGeometry.AbelianScheme.TateComparison.BaseChange.endSchemeMap_add, AlgebraicGeometry.AbelianScheme.TateComparison.BaseChange.endSchemeMap_one, ih, pow_succ]

variable {R : Type u} [CommRing R] {g N : ℕ}
    (P : AlgebraicGeometry.AbelianScheme.TateComparison.PEL.PELFamilyData R g N S) (c : R →+* R) (hP : P.IsRosatiCompatible c)

include hP in
theorem pel_scalar_poincare_dual (n : ℕ) :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass
      (𝟙 P.dual.abelian.scheme ⊗ₘ ((𝟙 P.abelian.scheme) ^ n)).left
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf P.dual.poincare) =
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass
      (((𝟙 P.dual.abelian.scheme) ^ n) ⊗ₘ 𝟙 P.abelian.scheme).left
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf P.dual.poincare) := by
  obtain ⟨d, hd, he⟩ := hP (n : R)
  rw [map_natCast, map_natCast, pelEndSchemeMap_natCast] at he
  have hd' : AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap P.dual.abelian.scheme d = (𝟙 P.dual.abelian.scheme) ^ n := by
    have := AlgebraicGeometry.AbelianScheme.CentralAction.Quotient.Construction.isogeny_effectiveEpi P.polarizationMap
    apply (cancel_epi P.polarizationMap.hom).mp
    rw [he, MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id]
  change AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass
    (𝟙 P.dual.abelian.scheme ⊗ₘ AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap P.abelian.scheme (P.action (n : R))).left _ = _ at hd
  rw [map_natCast, pelEndSchemeMap_natCast, hd'] at hd
  exact hd

include hP in
theorem pel_scalar_picard_dual (n : ℕ) :
    AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap ((𝟙 P.abelian.scheme) ^ n) P.dual P.dual =
      (𝟙 P.dual.abelian.scheme) ^ n :=
  (AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardAdjoints.Construction.NativePicardPullback.dualMap_eq_of_poincare ((𝟙 P.abelian.scheme) ^ n)
    P.dual P.dual ((𝟙 P.dual.abelian.scheme) ^ n) (pel_scalar_poincare_dual P c hP n).symm).symm

end

end OAI.RepresentationTheory.Theta.Geometric.PELMultiplicationDual
