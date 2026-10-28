import OAI.NumberTheory.PadicHodge.IntegralComparison.TerminalSectionRestriction
import OAI.NumberTheory.PadicHodge.PeriodInvariants.BigEtaleCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.ConnectedComponents

/-! # Degree Zero General Pullback -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.DegreeZeroGeneralPullback

noncomputable section

/-! Arbitrary original rational étale pullbacks in degree zero are precomposition on actual continuous sections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.AlgebraicGeometry Opposite _root_.TopologicalSpace

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.Cohomology OAI.NumberTheory.PadicHodge.PeriodInvariants.BigEtaleCohomology

variable (ℓ : ℕ) [Fact ℓ.Prime]

def sectionsEquiv (X : Scheme.{u}) : PeriodInvariants.BigEtaleCohomology.Cohomology ℓ X 0 ≃ₗ[Cohomology.Coeff.{u} ℓ] C(X, Cohomology.Coeff.{u} ℓ) :=
  PeriodInvariants.DegreeZeroSections.degreeZeroEquiv (Scheme.proetaleTopology.over X) (Cohomology.Coeff.{u} ℓ)
    Over.mkIdTerminal (PeriodInvariants.BigEtaleCohomology.coefficientSheaf ℓ X)

theorem comparison_sections (X : Scheme.{u}) (z : PeriodInvariants.BigEtaleCohomology.Cohomology ℓ X 0) :
    PeriodInvariants.EtaleDegreeZero.sectionsEquiv ℓ X (PeriodInvariants.BigEtaleCohomology.comparison ℓ X 0 z) = sectionsEquiv ℓ X z := by
  have h := TerminalSectionRestriction.cohomology (Scheme.ProEt.topology X)
    (Scheme.proetaleTopology.over X) (Cohomology.Coeff.{u} ℓ) (PeriodInvariants.EtaleDegreeZero.identityTerminal X)
    Over.mkIdTerminal (Scheme.ProEt.forget X) (PeriodInvariants.BigEtaleCohomology.coefficientSheaf ℓ X) z
  change PeriodInvariants.EtaleDegreeZero.sectionsEquiv ℓ X
    (((Ext.mk₀ (PeriodInvariants.BigEtaleCohomology.constantComparison ℓ X).inv).comp
      (z.mapExactFunctor (PeriodInvariants.BigProEtaleSite.restriction ℓ X)) (Nat.zero_add 0)).comp
        (Ext.mk₀ (𝟙 _)) (Nat.add_zero 0)) = _
  rw [Ext.comp_mk₀_id]
  apply h.trans
  apply ContinuousMap.ext
  intro x
  change sectionsEquiv ℓ X z ((Over.mkIdTerminal.from
    ((Scheme.ProEt.forget X).obj (Scheme.ProEt.mk (𝟙 X)))).left x) = sectionsEquiv ℓ X z x
  rw [Over.mkIdTerminal_from_left]
  rfl

theorem big_pullback_sections {X Y : Scheme.{u}} (g : X ⟶ Y) (z : PeriodInvariants.BigEtaleCohomology.Cohomology ℓ Y 0) :
    sectionsEquiv ℓ X (PeriodInvariants.BigEtaleCohomology.bigPullback ℓ g 0 z) = (sectionsEquiv ℓ Y z).comp g.base.hom := by
  have h := TerminalSectionRestriction.cohomology (Scheme.proetaleTopology.over X)
    (Scheme.proetaleTopology.over Y) (Cohomology.Coeff.{u} ℓ)
    Over.mkIdTerminal Over.mkIdTerminal (Over.map g) (PeriodInvariants.BigEtaleCohomology.coefficientSheaf ℓ Y) z
  change sectionsEquiv ℓ X
    (((Ext.mk₀ (PeriodInvariants.BigEtaleCohomology.constantTransport ℓ g).inv).comp
      (z.mapExactFunctor (PeriodInvariants.BigEtaleCohomology.pullbackFunctor ℓ g)) (Nat.zero_add 0)).comp
        (Ext.mk₀ (𝟙 _)) (Nat.add_zero 0)) = _
  rw [Ext.comp_mk₀_id]
  apply h.trans
  apply ContinuousMap.ext
  intro x
  change sectionsEquiv ℓ Y z ((Over.mkIdTerminal.from
    ((Over.map g).obj (Over.mk (𝟙 X)))).left x) = sectionsEquiv ℓ Y z (g x)
  rw [Over.mkIdTerminal_from_left]
  rfl

theorem pullback_sections {X Y : Scheme.{u}} (g : X ⟶ Y) (z : Cohomology.RationalEllAdicCohomology ℓ Y 0) :
    PeriodInvariants.EtaleDegreeZero.sectionsEquiv ℓ X (PeriodInvariants.BigEtaleCohomology.pullback ℓ g 0 z) =
      (PeriodInvariants.EtaleDegreeZero.sectionsEquiv ℓ Y z).comp g.base.hom := by
  obtain ⟨w, rfl⟩ := (PeriodInvariants.BigEtaleCohomology.comparisonEquiv ℓ Y 0).surjective z
  change PeriodInvariants.EtaleDegreeZero.sectionsEquiv ℓ X
    (PeriodInvariants.BigEtaleCohomology.comparison ℓ X 0 (PeriodInvariants.BigEtaleCohomology.bigPullback ℓ g 0 ((PeriodInvariants.BigEtaleCohomology.comparisonEquiv ℓ Y 0).symm (PeriodInvariants.BigEtaleCohomology.comparisonEquiv ℓ Y 0 w)))) = _
  rw [LinearEquiv.symm_apply_apply, comparison_sections, big_pullback_sections]
  exact congrArg (fun s => s.comp g.base.hom) (comparison_sections ℓ Y w).symm

theorem pullback_components {X Y : Scheme.{u}} [NoetherianSpace X] [NoetherianSpace Y]
    (g : X ⟶ Y) (z : Cohomology.RationalEllAdicCohomology ℓ Y 0) (c : _root_.ConnectedComponents X) :
    Etale.ConnectedComponents.equiv ℓ X (PeriodInvariants.BigEtaleCohomology.pullback ℓ g 0 z) c =
      Etale.ConnectedComponents.equiv ℓ Y z (ConnectedComponentSections.map g.base.hom c) := by
  obtain ⟨x, rfl⟩ := _root_.ConnectedComponents.surjective_coe c
  exact congrArg ULift.down (congrArg (fun s => s x) (pullback_sections ℓ g z))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.DegreeZeroGeneralPullback
