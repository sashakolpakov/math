import OAI.AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechShort
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorProducts

/-! # Model Ordinary Base Change -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModelOrdinaryBaseChange

noncomputable section

/-! A universally valid ordered Cech model remains a cohomology model in
ordinary coordinates after scalar extension. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace Construction.OrderedCechShortComparison

variable {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
variable {D : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
variable (φ : D ⟶ SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U)

theorem baseChange_quasiIso {A : Type u} [CommRing A] (a : Γ(S, ⊤) →+* A)
    [QuasiIsoAt (((ModuleCat.extendScalars a).mapHomologicalComplex (ComplexShape.up ℕ)).map φ) 1] :
    ShortComplex.QuasiIso ((ModuleCat.extendScalars a).mapShortComplex.map (OrderedCechShort.Construction.OrderedCechShortComparison.comparison π M U φ)) := by
  let F := ModuleCat.extendScalars a
  let H := F.mapHomologicalComplex (ComplexShape.up ℕ)
  let e := F.mapHomotopyEquiv (SheafCohomology.Projective.BaseCechHomotopyEquiv.Scheme.Modules.baseCechOrderedHomotopyEquiv π M U)
  have : QuasiIsoAt (H.map (SheafCohomology.Projective.BaseCechHomotopyEquiv.Scheme.Modules.baseCechOrderedHomotopyEquiv π M U).inv) 1 := e.quasiIsoAt_inv 1
  have hq : QuasiIsoAt (H.map (φ ≫ (SheafCohomology.Projective.BaseCechHomotopyEquiv.Scheme.Modules.baseCechOrderedHomotopyEquiv π M U).inv)) 1 := by
    rw [H.map_comp]
    infer_instance
  have hs := (quasiIsoAt_iff' (H.map (φ ≫ (SheafCohomology.Projective.BaseCechHomotopyEquiv.Scheme.Modules.baseCechOrderedHomotopyEquiv π M U).inv))
    0 1 2 (by simp) (by simp)).mp hq
  change ShortComplex.QuasiIso (F.mapShortComplex.map (_ ≫ _))
  rw [Functor.map_comp]
  have : ShortComplex.QuasiIso (F.mapShortComplex.map
      ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} Γ(S, ⊤))
        (ComplexShape.up ℕ) 0 1 2).map (φ ≫ (SheafCohomology.Projective.BaseCechHomotopyEquiv.Scheme.Modules.baseCechOrderedHomotopyEquiv π M U).inv))) := hs
  exact ShortComplex.quasiIso_comp _ _

end Construction.OrderedCechShortComparison

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModelOrdinaryBaseChange
