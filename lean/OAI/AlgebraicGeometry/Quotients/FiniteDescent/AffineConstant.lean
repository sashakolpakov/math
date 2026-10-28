import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ConstantCohomology
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechAffineBaseChange
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.FieldPoint
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Affine Constant -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineConstant

noncomputable section

/-! A constant geometric family has a finite free detector for its first
Cech cohomology, with arbitrary further base change. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace Construction.AffineConstantDetector

variable {K : Type u} [Field K] {X Y T : Scheme.{u}} [IsAffine T]
variable (f : Y ⟶ X) (π : X ⟶ Spec (.of K)) (ρ : Y ⟶ T) (g : T ⟶ Spec (.of K))
variable (hp : IsPullback f ρ π g) (M : X.Modules) [M.IsQuasicoherent]
variable {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
variable (ha : ∀ (q : ℕ) (i : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q), IsAffineOpen (∏ᶜ fun k => U (i.1 k)))

abbrev source := (SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).sc' 0 1 2
abbrev family := (CechBaseTmul.Construction.CechBaseChangeMap.target f ρ M U).sc' 0 1 2
abbrev target : ShortComplex (ModuleCat.{u} Γ(T, ⊤)) :=
  letI : Field Γ(Spec (.of K), ⊤) := FieldPoint.Construction.FieldPointPrime.sectionsField K
  ConstantCohomology.Construction.ConstantCohomologyDetector.target g.appTop.hom (source π M U)

def shortIso : ((source π M U).map (ModuleCat.extendScalars g.appTop.hom)) ≅ family f ρ M U := by
  have := CechAffineBaseChange.Construction.CechBaseChangeMap.isIso_of_affine_intersections f π ρ g hp M U ha
  exact (HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} Γ(T, ⊤))
    (ComplexShape.up ℕ) 0 1 2).mapIso (asIso (CechBaseTmul.Construction.CechBaseChangeMap.map f π ρ g hp.w M U))

def comparison : family f ρ M U ⟶ target π g M U := by
  letI : Field Γ(Spec (.of K), ⊤) := FieldPoint.Construction.FieldPointPrime.sectionsField K
  exact ConstantCohomology.Construction.ConstantCohomologyDetector.comparison g.appTop.hom (source π M U)
    (shortIso f π ρ g hp M U ha)

theorem incoming_zero : (family f ρ M U).f ≫ (comparison f π ρ g hp M U ha).τ₂ = 0 := by
  let : Field Γ(Spec (.of K), ⊤) := FieldPoint.Construction.FieldPointPrime.sectionsField K
  rw [← (comparison f π ρ g hp M U ha).comm₁₂,
    ConstantCohomology.Construction.ConstantCohomologyDetector.first_zero, comp_zero]

omit [IsAffine T] [M.IsQuasicoherent] [Finite ι] in
theorem finite [Module.Finite Γ(Spec (.of K), ⊤) ((SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).homology 1)] :
    Module.Finite Γ(T, ⊤) (target π g M U).X₂ := by
  let : Field Γ(Spec (.of K), ⊤) := FieldPoint.Construction.FieldPointPrime.sectionsField K
  have : Module.Finite Γ(Spec (.of K), ⊤) (source π M U).homology :=
    Module.Finite.equiv ((SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).homologyIsoSc' 0 1 2
      (by simp) (by simp)).toLinearEquiv
  exact ConstantCohomology.Construction.ConstantCohomologyDetector.finite g.appTop.hom (source π M U)

omit [IsAffine T] [M.IsQuasicoherent] [Finite ι] in
theorem free : Module.Free Γ(T, ⊤) (target π g M U).X₂ := by
  let : Field Γ(Spec (.of K), ⊤) := FieldPoint.Construction.FieldPointPrime.sectionsField K
  exact ConstantCohomology.Construction.ConstantCohomologyDetector.free g.appTop.hom (source π M U)

theorem baseChange_quasiIso {A : Type u} [CommRing A] (a : Γ(T, ⊤) →+* A) :
    ShortComplex.QuasiIso ((ModuleCat.extendScalars a).mapShortComplex.map
      (comparison f π ρ g hp M U ha)) := by
  let : Field Γ(Spec (.of K), ⊤) := FieldPoint.Construction.FieldPointPrime.sectionsField K
  exact ConstantCohomology.Construction.ConstantCohomologyDetector.baseChange_quasiIso g.appTop.hom (source π M U)
    (shortIso f π ρ g hp M U ha) a

end Construction.AffineConstantDetector

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineConstant
