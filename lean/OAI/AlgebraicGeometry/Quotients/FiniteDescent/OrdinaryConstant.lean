import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineConstant
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.OrdinaryCechBase

/-! # Ordinary Constant -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.OrdinaryConstant

noncomputable section

/-! The constant-family detector on actual ordinary Cech section coordinates. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace Construction.OrdinaryConstantDetector

variable {K : Type u} [Field K] {X Y T : Scheme.{u}} [IsAffine T]
variable (f : Y ⟶ X) (π : X ⟶ Spec (.of K)) (ρ : Y ⟶ T) (g : T ⟶ Spec (.of K))
variable (hp : IsPullback f ρ π g) (M : X.Modules) [M.IsQuasicoherent]
variable {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
variable (ha : ∀ (q : ℕ) (i : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q), IsAffineOpen (∏ᶜ fun k => U (i.1 k)))

abbrev source := CechShort.Construction.CechShortCoordinates.target ρ ((Scheme.Modules.pullback f).obj M)
  (fun i => f ⁻¹ᵁ U i)

def comparison : source f ρ M U ⟶ AffineConstant.Construction.AffineConstantDetector.target π g M U :=
  OrdinaryCechBase.Construction.OrdinaryCechProjection.map ρ ((Scheme.Modules.pullback f).obj M) (fun i => f ⁻¹ᵁ U i) ≫
    AffineConstant.Construction.AffineConstantDetector.comparison f π ρ g hp M U ha

theorem incoming_zero : (source f ρ M U).f ≫ (comparison f π ρ g hp M U ha).τ₂ = 0 := by
  let : Field Γ(Spec (.of K), ⊤) := FieldPoint.Construction.FieldPointPrime.sectionsField K
  rw [← (comparison f π ρ g hp M U ha).comm₁₂,
    ConstantCohomology.Construction.ConstantCohomologyDetector.first_zero, comp_zero]

theorem baseChange_quasiIso {A : Type u} [CommRing A] (a : Γ(T, ⊤) →+* A) :
    ShortComplex.QuasiIso ((ModuleCat.extendScalars a).mapShortComplex.map
      (comparison f π ρ g hp M U ha)) := by
  have := OrdinaryCechBase.Construction.OrdinaryCechProjection.baseChange_quasiIso ρ ((Scheme.Modules.pullback f).obj M)
    (fun i => f ⁻¹ᵁ U i) a
  have := AffineConstant.Construction.AffineConstantDetector.baseChange_quasiIso f π ρ g hp M U ha a
  change ShortComplex.QuasiIso ((ModuleCat.extendScalars a).mapShortComplex.map (_ ≫ _))
  rw [Functor.map_comp]
  exact ShortComplex.quasiIso_comp _ _

end Construction.OrdinaryConstantDetector

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.OrdinaryConstant
