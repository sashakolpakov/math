import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechShort
import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechHomotopyEquiv
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.HomologyInjective
import Mathlib.Algebra.Homology.QuasiIso

/-! # Ordered Cech Short -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechShort

noncomputable section

/-! A model of ordered Cech cohomology maps to ordinary section
coordinates and detects boundaries in degree one. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace Construction.OrderedCechShortComparison

variable {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
variable {D : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
variable (φ : D ⟶ SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U)

def comparison : D.sc' 0 1 2 ⟶ CechShort.Construction.CechShortCoordinates.target π M U :=
  (HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} Γ(S, ⊤)) (ComplexShape.up ℕ) 0 1 2).map
    (φ ≫ (SheafCohomology.Projective.BaseCechHomotopyEquiv.Scheme.Modules.baseCechOrderedHomotopyEquiv π M U).inv) ≫ (CechShort.Construction.CechShortCoordinates.iso π M U).hom

theorem quasiIso [QuasiIsoAt φ 1] : ShortComplex.QuasiIso (comparison π M U φ) := by
  have : QuasiIsoAt (φ ≫ (SheafCohomology.Projective.BaseCechHomotopyEquiv.Scheme.Modules.baseCechOrderedHomotopyEquiv π M U).inv) 1 := inferInstance
  have := (quasiIsoAt_iff' (φ ≫ (SheafCohomology.Projective.BaseCechHomotopyEquiv.Scheme.Modules.baseCechOrderedHomotopyEquiv π M U).inv)
    0 1 2 (by simp) (by simp)).mp this
  exact ShortComplex.quasiIso_comp _ _

theorem middle (z : D.X 1) :
    (comparison π M U φ).τ₂ z = CechTuplePi.Construction.CechTupleCoordinates.one π M U
      ((SheafCohomology.Projective.BaseCechHomotopyEquiv.Scheme.Modules.baseCechOrderedHomotopyEquiv π M U).inv.f 1 (φ.f 1 z)) := rfl

theorem boundary [QuasiIsoAt φ 1] (z : D.X 1) (hz : D.d 1 2 z = 0)
    (hb : (comparison π M U φ).τ₂ z ∈ (CechShort.Construction.CechShortCoordinates.target π M U).f.hom.range) :
    z ∈ (D.d 0 1).hom.range := by
  have := quasiIso π M U φ
  exact HomologyInjective.Construction.HomologyInjectiveCriterion.boundary (comparison π M U φ)
    ((ModuleCat.mono_iff_injective _).mp inferInstance) z hz hb

end Construction.OrderedCechShortComparison

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechShort
