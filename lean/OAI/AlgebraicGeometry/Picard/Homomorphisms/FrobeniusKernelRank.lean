import OAI.AlgebraicGeometry.Picard.Homomorphisms.FrobeniusDegree
import OAI.AlgebraicGeometry.Picard.Homomorphisms.Kernel

/-! # Frobenius Kernel Rank -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.FrobeniusKernelRank

noncomputable section

/-! The scheme-theoretic Frobenius kernel has rank p^d, including all nilpotents. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

theorem kernelScheme_finrank {S : Scheme.{u}} {A B : Over S} [GrpObj B]
    (q : A ⟶ B) [Flat q.left] [IsFinite q.left] (s : S) :
    (Kernel.Construction.kernelScheme q).hom.finrank s = q.left.finrank ((MonObj.one (X := B)).left s) := by
  have H := (Kernel.Construction.kernelScheme_isPullback q).map (Over.forget S)
  change IsPullback (Kernel.Construction.kernelInclusion q).left (Kernel.Construction.kernelScheme q).hom q.left (MonObj.one (X := B)).left at H
  exact Scheme.Hom.finrank_of_isPullback (Kernel.Construction.kernelInclusion q).left (Kernel.Construction.kernelScheme q).hom q.left
    (MonObj.one (X := B)).left H s

theorem relativeFrobenius_kernel_finrank
    (p : ℕ) (hp : p.Prime) {S : Scheme.{u}} (hS : (p : Γ(S, ⊤)) = 0)
    (A : Over S) [GrpObj A] (d : ℕ) [SmoothOfRelativeDimension d A.hom] (s : S) :
    (Kernel.Construction.kernelScheme (Frobenius.Construction.relativeFrobenius p hp hS A)).hom.finrank s = p ^ d := by
  have : Smooth A.hom := SmoothOfRelativeDimension.smooth d A.hom
  have : Flat (Frobenius.Construction.relativeFrobenius p hp hS A).left := Homomorphisms.Smooth.Construction.relativeFrobenius_smooth_flat p hp hS A
  rw [kernelScheme_finrank]
  exact FrobeniusDegree.Construction.relativeFrobenius_smooth_finrank p hp hS A d _

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.FrobeniusKernelRank
