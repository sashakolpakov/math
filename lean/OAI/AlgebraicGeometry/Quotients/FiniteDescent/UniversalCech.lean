import OAI.AlgebraicGeometry.Quotients.FiniteDescent.OrdinaryConstant

/-! # Universal Cech -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.UniversalCech

noncomputable section

/-! A finite free cohomology detector and its construction for a constant
geometric family, valid after every scalar extension. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace Construction.UniversalCechDetector

structure Data (R : Type u) [CommRing R] (T : ShortComplex (ModuleCat.{u} R)) where
  target : ShortComplex (ModuleCat.{u} R)
  comparison : T ⟶ target
  first_zero : target.f = 0
  finite : Module.Finite R target.X₂
  free : Module.Free R target.X₂
  baseChange : ∀ {A : Type u} [CommRing A] (a : R →+* A),
    ShortComplex.QuasiIso ((ModuleCat.extendScalars a).mapShortComplex.map comparison)

variable {K : Type u} [Field K] {X Y S : Scheme.{u}} [IsAffine S]
variable (f : Y ⟶ X) (π : X ⟶ Spec (.of K)) (ρ : Y ⟶ S) (t : S ⟶ Spec (.of K))
variable (hp : IsPullback f ρ π t) (M : X.Modules) [M.IsQuasicoherent]
variable {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
variable (ha : ∀ (q : ℕ) (i : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q), IsAffineOpen (∏ᶜ fun k => U (i.1 k)))
variable [Module.Finite Γ(Spec (.of K), ⊤) ((SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).homology 1)]

def ofConstantFamily : Data Γ(S, ⊤) (OrdinaryConstant.Construction.OrdinaryConstantDetector.source f ρ M U) where
  target := AffineConstant.Construction.AffineConstantDetector.target π t M U
  comparison := OrdinaryConstant.Construction.OrdinaryConstantDetector.comparison f π ρ t hp M U ha
  first_zero := by
    let : Field Γ(Spec (.of K), ⊤) := FieldPoint.Construction.FieldPointPrime.sectionsField K
    exact ConstantCohomology.Construction.ConstantCohomologyDetector.first_zero t.appTop.hom (AffineConstant.Construction.AffineConstantDetector.source π M U)
  finite := AffineConstant.Construction.AffineConstantDetector.finite π t M U
  free := AffineConstant.Construction.AffineConstantDetector.free π t M U
  baseChange := OrdinaryConstant.Construction.OrdinaryConstantDetector.baseChange_quasiIso f π ρ t hp M U ha

end Construction.UniversalCechDetector

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.UniversalCech
