import OAI.AlgebraicGeometry.Quotients.FiniteDescent.FieldHomology
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.FieldExtension
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Finite
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.HomologyInjective

/-! # Constant Cohomology -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ConstantCohomology

noncomputable section

/-! A scalar extension of a field complex has a finite free cohomology
detector, valid under every further scalar extension. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace Construction.ConstantCohomologyDetector

variable {K R : Type u} [Field K] [CommRing R] (f : K →+* R)
variable (C : ShortComplex (ModuleCat.{u} K))
variable {T : ShortComplex (ModuleCat.{u} R)}
variable (e : (C.map (ModuleCat.extendScalars f)) ≅ T)

def target : ShortComplex (ModuleCat.{u} R) :=
  (FieldHomology.Construction.FieldHomologyProjection.target C).map (ModuleCat.extendScalars f)

def comparison : T ⟶ target f C :=
  e.inv ≫ (ModuleCat.extendScalars f).mapShortComplex.map (FieldHomology.Construction.FieldHomologyProjection.map C)

theorem first_zero : (target f C).f = 0 := by
  change (ModuleCat.extendScalars f).map 0 = 0
  exact (ModuleCat.extendScalars f).map_zero _ _

theorem second_zero : (target f C).g = 0 := by
  change (ModuleCat.extendScalars f).map 0 = 0
  exact (ModuleCat.extendScalars f).map_zero _ _

theorem quasiIso : ShortComplex.QuasiIso (comparison f C e) := by
  have := FieldExtension.Construction.FieldExtensionExact.preservesHomology f
  have := FieldHomology.Construction.FieldHomologyProjection.quasiIso C
  exact ShortComplex.quasiIso_comp _ _

theorem finite [Module.Finite K C.homology] : Module.Finite R (target f C).X₂ := by
  let : Algebra K R := f.toAlgebra
  have := FieldHomology.Construction.FieldHomologyProjection.finite C
  exact inferInstanceAs (Module.Finite R (R ⊗[K] FieldHomology.Construction.FieldHomologyProjection.H C))

theorem free : Module.Free R (target f C).X₂ := by
  let : Algebra K R := f.toAlgebra
  exact inferInstanceAs (Module.Free R (R ⊗[K] FieldHomology.Construction.FieldHomologyProjection.H C))

theorem baseChange_quasiIso {A : Type u} [CommRing A] (g : R →+* A) :
    ShortComplex.QuasiIso ((ModuleCat.extendScalars g).mapShortComplex.map (comparison f C e)) := by
  let F := ModuleCat.extendScalars f
  let G := ModuleCat.extendScalars g
  have : (F ⋙ G).PreservesHomology := FieldExtension.Construction.FieldExtensionExact.preservesHomology_of_leftAdjoint (F ⋙ G)
  have := FieldHomology.Construction.FieldHomologyProjection.quasiIso C
  have hq : ShortComplex.QuasiIso ((F ⋙ G).mapShortComplex.map (FieldHomology.Construction.FieldHomologyProjection.map C)) :=
    inferInstance
  change ShortComplex.QuasiIso (G.mapShortComplex.map (e.inv ≫ F.mapShortComplex.map _))
  rw [Functor.map_comp]
  have : ShortComplex.QuasiIso (G.mapShortComplex.map (F.mapShortComplex.map
      (FieldHomology.Construction.FieldHomologyProjection.map C))) := hq
  exact ShortComplex.quasiIso_comp _ _

theorem detects {A : Type u} [CommRing A] (g : R →+* A)
    (z : (T.map (ModuleCat.extendScalars g)).X₂)
    (hz : (T.map (ModuleCat.extendScalars g)).g z = 0)
    (hb : ((ModuleCat.extendScalars g).mapShortComplex.map (comparison f C e)).τ₂ z = 0) :
    z ∈ (T.map (ModuleCat.extendScalars g)).f.hom.range := by
  have := baseChange_quasiIso f C e g
  exact HomologyInjective.Construction.HomologyInjectiveCriterion.boundary
    ((ModuleCat.extendScalars g).mapShortComplex.map (comparison f C e))
    ((ModuleCat.mono_iff_injective _).mp inferInstance) z hz
    ⟨0, (map_zero _).trans hb.symm⟩

end Construction.ConstantCohomologyDetector

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ConstantCohomology
