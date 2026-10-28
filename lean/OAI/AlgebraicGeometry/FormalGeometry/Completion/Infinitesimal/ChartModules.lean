import OAI.AlgebraicGeometry.FormalGeometry.Completion.RelativeStructureSections
import OAI.AlgebraicGeometry.FormalGeometry.Completion.QuotientPushoutLinear

/-! # Chart Modules -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Infinitesimal.ChartModules.Construction

noncomputable section

/-! The affine infinitesimal chart comparison as a linear equivalence over the literal base ring. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {R : Type u} [CommRing R] (I : Ideal R)
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))

/-- The actual affine infinitesimal sections are the corresponding module quotient. -/
def affineInfinitesimalSectionsModuleEquiv (n : ℕ) (U : X.Opens) (hU : IsAffineOpen U) :
    ((RelativeStructureSections.Construction.relativeStructureSections f).obj (op U) ⧸
      (I ^ (n + 1) • ⊤ : Submodule R ((RelativeStructureSections.Construction.relativeStructureSections f).obj (op U)))) ≃ₗ[R]
      (RelativeStructureSections.Construction.relativeStructureSections (pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I n) ≫ f)).obj
        (op (pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I n) ⁻¹ᵁ U)) := by
  let g := pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I n)
  let : Algebra R Γ(X, U) := (Affine.InfinitesimalSections.Construction.baseOpenSectionsMap f U).toAlgebra
  let : Algebra R Γ(Neighborhoods.Construction.infinitesimalNeighborhood I f n, g ⁻¹ᵁ U) :=
    (Affine.InfinitesimalSections.Construction.baseOpenSectionsMap (g ≫ f) (g ⁻¹ᵁ U)).toAlgebra
  let a : Γ(X, U) →ₐ[R] Γ(Neighborhoods.Construction.infinitesimalNeighborhood I f n, g ⁻¹ᵁ U) :=
    { (g.app U).hom with
      commutes' := fun r => RingHom.congr_fun (RelativeStructureSections.Construction.baseOpenSectionsMap_comp f g U) r }
  exact QuotientPushoutLinear.Construction.quotientPushoutLinearEquiv (R := R) (S := Γ(X, U))
    (T := Γ(Neighborhoods.Construction.infinitesimalNeighborhood I f n, g ⁻¹ᵁ U)) (I ^ (n + 1)) a
    (Affine.InfinitesimalSections.Construction.infinitesimalOpenBaseSectionsMap I f n U).hom
    (Affine.InfinitesimalSections.Construction.affineInfinitesimalSections_isPushout I f n U hU)

theorem affineInfinitesimalSectionsModuleEquiv_mk (n : ℕ) (U : X.Opens) (hU : IsAffineOpen U)
    (s : (RelativeStructureSections.Construction.relativeStructureSections f).obj (op U)) :
    affineInfinitesimalSectionsModuleEquiv I f n U hU (Submodule.Quotient.mk s) =
      (RelativeStructureSections.Construction.relativeStructureSectionsPullback f (pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I n))).app (op U) s := by
  let g := pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I n)
  let : Algebra R Γ(X, U) := (Affine.InfinitesimalSections.Construction.baseOpenSectionsMap f U).toAlgebra
  let : Algebra R Γ(Neighborhoods.Construction.infinitesimalNeighborhood I f n, g ⁻¹ᵁ U) :=
    (Affine.InfinitesimalSections.Construction.baseOpenSectionsMap (g ≫ f) (g ⁻¹ᵁ U)).toAlgebra
  unfold affineInfinitesimalSectionsModuleEquiv
  exact QuotientPushoutLinear.Construction.quotientPushoutLinearEquiv_mk (R := R) (S := Γ(X, U))
    (T := Γ(Neighborhoods.Construction.infinitesimalNeighborhood I f n, g ⁻¹ᵁ U)) _ _ _ _ s

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Infinitesimal.ChartModules.Construction
