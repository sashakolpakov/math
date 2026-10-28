import OAI.AlgebraicGeometry.Picard.Homomorphisms.FrobeniusKernelRank
import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Kernel Geometry -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelGeometry

noncomputable section

/-! The relative Frobenius kernel has one underlying point on every geometric fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

theorem geometricallyConnected_of_radicial_surjective {X Y : Scheme.{u}}
    (f : X ⟶ Y) [UniversallyInjective f] [Surjective f] : GeometricallyConnected f := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ s => ?_⟩
  have : UniversallyInjective (pullback.snd f s) :=
    MorphismProperty.pullback_snd (P := @UniversallyInjective) f s inferInstance
  have : Subsingleton (pullback f s : Scheme.{u}) := (pullback.snd f s).injective.subsingleton
  obtain ⟨x, _⟩ := (pullback.snd f s).surjective (IsLocalRing.closedPoint K)
  have : Nonempty (pullback f s : Scheme.{u}) := ⟨x⟩
  exact ⟨inferInstance⟩

theorem kernelScheme_universallyInjective {S : Scheme.{u}} {A B : Over S} [GrpObj B]
    (q : A ⟶ B) [UniversallyInjective q.left] : UniversallyInjective (Kernel.Construction.kernelScheme q).hom := by
  have H := (Kernel.Construction.kernelScheme_isPullback q).map (Over.forget S)
  change IsPullback (Kernel.Construction.kernelInclusion q).left (Kernel.Construction.kernelScheme q).hom q.left η[B].left at H
  exact MorphismProperty.of_isPullback (P := @UniversallyInjective) H inferInstance

theorem kernelScheme_surjective {S : Scheme.{u}} {A B : Over S} [GrpObj B]
    (q : A ⟶ B) [Surjective q.left] : Surjective (Kernel.Construction.kernelScheme q).hom := by
  have H := (Kernel.Construction.kernelScheme_isPullback q).map (Over.forget S)
  change IsPullback (Kernel.Construction.kernelInclusion q).left (Kernel.Construction.kernelScheme q).hom q.left η[B].left at H
  exact MorphismProperty.of_isPullback (P := @Surjective) H inferInstance

theorem relativeFrobenius_kernel_geometricallyConnected
    (p : ℕ) (hp : p.Prime) {S : Scheme.{u}} (hS : (p : Γ(S, ⊤)) = 0)
    (A : Over S) [GrpObj A] :
    GeometricallyConnected (Kernel.Construction.kernelScheme (Frobenius.Construction.relativeFrobenius p hp hS A)).hom := by
  have := kernelScheme_universallyInjective (Frobenius.Construction.relativeFrobenius p hp hS A)
  have := kernelScheme_surjective (Frobenius.Construction.relativeFrobenius p hp hS A)
  exact geometricallyConnected_of_radicial_surjective _

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelGeometry
