import OAI.AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechShort
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorProducts

/-! # Ordinary Cech Base -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.OrdinaryCechBase

noncomputable section

/-! Projection from ordinary Cech coordinates to the ordered complex remains
a cohomology equivalence under every scalar extension. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace Construction.OrdinaryCechProjection

variable {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

abbrev target := (SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).sc' 0 1 2

def map : CechShort.Construction.CechShortCoordinates.target π M U ⟶ target π M U :=
  (CechShort.Construction.CechShortCoordinates.iso π M U).inv ≫
    (HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} Γ(S, ⊤))
      (ComplexShape.up ℕ) 0 1 2).map (SheafCohomology.Projective.BaseCechHomotopyEquiv.Scheme.Modules.baseCechOrderedHomotopyEquiv π M U).hom

theorem baseChange_quasiIso {A : Type u} [CommRing A] (a : Γ(S, ⊤) →+* A) :
    ShortComplex.QuasiIso ((ModuleCat.extendScalars a).mapShortComplex.map (OrdinaryCechProjection.map π M U)) := by
  let F := ModuleCat.extendScalars a
  let e := F.mapHomotopyEquiv (SheafCohomology.Projective.BaseCechHomotopyEquiv.Scheme.Modules.baseCechOrderedHomotopyEquiv π M U)
  have hq : QuasiIsoAt e.hom 1 := inferInstance
  have hs := (quasiIsoAt_iff' e.hom 0 1 2 (by simp) (by simp)).mp hq
  change ShortComplex.QuasiIso (F.mapShortComplex.map (_ ≫ _))
  rw [Functor.map_comp]
  have : ShortComplex.QuasiIso (F.mapShortComplex.map
      ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} Γ(S, ⊤))
        (ComplexShape.up ℕ) 0 1 2).map (SheafCohomology.Projective.BaseCechHomotopyEquiv.Scheme.Modules.baseCechOrderedHomotopyEquiv π M U).hom)) := hs
  exact ShortComplex.quasiIso_comp _ _

end Construction.OrdinaryCechProjection

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.OrdinaryCechBase
