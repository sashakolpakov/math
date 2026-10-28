import OAI.AlgebraicGeometry.Resolution.Blowups.Global.HomogenizationRestriction
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalComponent.Center

/-! # Homogenization -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Homogenization preserves the actual canonical component center on the global atlas. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

section

universe u

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] {J : Ideal R} {n : ℕ}

def Component.CenterChoice.Construction.ComponentCenterChoice.homogenize (C : Component.CenterChoice.Construction.ComponentCenterChoice k R J n) :
    Component.CenterChoice.Construction.ComponentCenterChoice k R (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) n := by
  cases C with
  | terminal ht => exact .terminal (by rwa [HomogenizationTangent.Construction.relativeHomogenizedIdeal_tangent])
  | normal z D hD hz => exact .normal z D hD (by rwa [HomogenizationTangent.Construction.relativeHomogenizedIdeal_tangent])

theorem Component.CenterChoice.Construction.ComponentCenterChoice.homogenize_center (C : Component.CenterChoice.Construction.ComponentCenterChoice k R J n) : C.homogenize.center = C.center := by
  cases C with
  | terminal _ => rfl
  | normal z D hD hz =>
      change Coefficient.ComponentNaturality.Construction.coefficientComponentCenter k z
        (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) n) (n + 1) = _
      rw [HomogenizationIdempotence.Construction.relativeHomogenizedIdeal_idempotent]
      rfl

end

namespace GlobalComponent

variable {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {J : X.IdealSheafData} {n : ℕ}

def ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.homogenize (A : ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) :
    ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f (Global.Homogenization.Construction.smoothHomogenizedIdealSheaf f J n) n :=
  { A with
    ideals := fun i => Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal ℂ (A.ideals i) n
    ideal_eq := fun i => Global.HomogenizationRestriction.Construction.smoothHomogenizedIdealSheaf_comap_affine f J n
      (A.map i) (A.ground i) (A.ideals i) (A.ideal_eq i)
    choice := fun i => (A.choice i).homogenize }

theorem ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.homogenize_center (A : ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) : A.homogenize.center = A.center := by
  apply A.existsUnique_center.choose_spec.2
  intro i
  have h := A.homogenize.center_restrict i
  change A.homogenize.center.comap (A.map i) = Affine.QuotientKernel.Construction.affineQuotientKernel (A.choice i).homogenize.center at h
  rwa [Component.CenterChoice.Construction.ComponentCenterChoice.homogenize_center] at h

end GlobalComponent

end

end OAI.AlgebraicGeometry.Resolution.Blowups
