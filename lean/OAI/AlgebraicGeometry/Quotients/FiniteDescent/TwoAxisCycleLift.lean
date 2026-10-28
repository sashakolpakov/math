import OAI.AlgebraicGeometry.Quotients.FiniteDescent.TwoAxis
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ScalarFunctor
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.FlatCycle
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Finite

/-! # Two Axis Cycle Lift -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.TwoAxisCycleLift

noncomputable section

/-! Fiber detection on two axes produces a section cycle over the
original ring through a flat local extension. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace Construction.FlatTwoAxisCycleLift

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable [IsLocalRing A] [Module.Flat R A]
variable (D C T₁ T₂ Q₁ Q₂ : ShortComplex (ModuleCat.{u} R))
variable [Module.Finite R D.X₁] [Module.Projective R D.X₁]
variable [Module.Finite R D.X₂] [Module.Projective R D.X₂]
variable [Module.Finite R D.X₃] [Module.Projective R D.X₃]
variable [Module.Finite R Q₁.X₂] [Module.Free R Q₁.X₂]
variable [Module.Finite R Q₂.X₂] [Module.Free R Q₂.X₂]

theorem exists_cycle (φ : D ⟶ C) (r₁ : C ⟶ T₁) (r₂ : C ⟶ T₂)
    (p₁ : T₁ ⟶ Q₁) (p₂ : T₂ ⟶ Q₂) (h₁ : Q₁.f = 0) (h₂ : Q₂.f = 0)
    [ShortComplex.QuasiIso ((ModuleCat.extendScalars
      ((algebraMap A (IsLocalRing.ResidueField A)).comp (algebraMap R A))).mapShortComplex.map φ)]
    [ShortComplex.QuasiIso ((ModuleCat.extendScalars
      ((algebraMap A (IsLocalRing.ResidueField A)).comp (algebraMap R A))).mapShortComplex.map p₁)]
    [ShortComplex.QuasiIso ((ModuleCat.extendScalars
      ((algebraMap A (IsLocalRing.ResidueField A)).comp (algebraMap R A))).mapShortComplex.map p₂)]
    (hj : CechBoundary.Construction.CechBoundaryTransport.JointlyDetects
      ((ModuleCat.extendScalars ((algebraMap A (IsLocalRing.ResidueField A)).comp
        (algebraMap R A))).mapShortComplex.map r₁)
      ((ModuleCat.extendScalars ((algebraMap A (IsLocalRing.ResidueField A)).comp
        (algebraMap R A))).mapShortComplex.map r₂))
    (z : IsLocalRing.ResidueField A ⊗[A] (A ⊗[R] D.X₁))
    (hz : (D.f.hom.baseChange A).baseChange (IsLocalRing.ResidueField A) z = 0) (hne : z ≠ 0) :
    ∃ x : D.X₁, D.f x = 0 ∧
      (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] ((1 : A) ⊗ₜ[R] x) ≠ 0 := by
  let f := algebraMap R A
  let g := algebraMap A (IsLocalRing.ResidueField A)
  let F₀ := ModuleBaseChangeComplex.Construction.LocalSectionLifting.moduleBaseChangeFunctor R A
  let F := F₀.mapShortComplex
  let G := (ModuleCat.extendScalars g).mapShortComplex
  let e := ModuleCat.extendScalarsComp f g ≪≫
    Functor.isoWhiskerRight (ScalarFunctor.Construction.ScalarFunctorComparison.iso R A).symm (ModuleCat.extendScalars g)
  let D' := F.obj D
  have : Module.Finite A D'.X₁ := inferInstanceAs (Module.Finite A (A ⊗[R] D.X₁))
  have : Module.Finite A D'.X₂ := inferInstanceAs (Module.Finite A (A ⊗[R] D.X₂))
  have : Module.Finite A D'.X₃ := inferInstanceAs (Module.Finite A (A ⊗[R] D.X₃))
  have : Module.Flat A D'.X₁ := inferInstanceAs (Module.Flat A (A ⊗[R] D.X₁))
  have : Module.Flat A D'.X₂ := inferInstanceAs (Module.Flat A (A ⊗[R] D.X₂))
  have : Module.Flat A D'.X₃ := inferInstanceAs (Module.Flat A (A ⊗[R] D.X₃))
  have : Module.Free A D'.X₁ := Module.free_of_flat_of_isLocalRing
  have : Module.Free A D'.X₂ := Module.free_of_flat_of_isLocalRing
  have : Module.Free A D'.X₃ := Module.free_of_flat_of_isLocalRing
  have : Module.Finite A (F.obj Q₁).X₂ := inferInstanceAs (Module.Finite A (A ⊗[R] Q₁.X₂))
  have : Module.Free A (F.obj Q₁).X₂ := inferInstanceAs (Module.Free A (A ⊗[R] Q₁.X₂))
  have : Module.Finite A (F.obj Q₂).X₂ := inferInstanceAs (Module.Finite A (A ⊗[R] Q₂.X₂))
  have : Module.Free A (F.obj Q₂).X₂ := inferInstanceAs (Module.Free A (A ⊗[R] Q₂.X₂))
  have : ShortComplex.QuasiIso (G.map (F.map φ)) := ShortComplexNatural.Construction.ShortComplexNaturalIso.quasiIso e φ
  have : ShortComplex.QuasiIso (G.map (F.map p₁)) := ShortComplexNatural.Construction.ShortComplexNaturalIso.quasiIso e p₁
  have : ShortComplex.QuasiIso (G.map (F.map p₂)) := ShortComplexNatural.Construction.ShortComplexNaturalIso.quasiIso e p₂
  have hd : CechBoundary.Construction.CechBoundaryTransport.JointlyDetects (G.map (F.map r₁)) (G.map (F.map r₂)) :=
    ShortComplexNatural.Construction.ShortComplexNaturalIso.jointly e r₁ r₂ hj
  have hf₁ : (F.obj Q₁).f = 0 := by
    change F₀.map Q₁.f = 0
    rw [h₁, Functor.map_zero]
  have hf₂ : (F.obj Q₂).f = 0 := by
    change F₀.map Q₂.f = 0
    rw [h₂, Functor.map_zero]
  obtain ⟨x, hx, he⟩ := TwoAxis.Construction.TwoAxisCycleLift.lift D' (F.obj C) (F.obj T₁) (F.obj T₂) (F.obj Q₁) (F.obj Q₂)
    (F.map φ) (F.map r₁) (F.map r₂) (F.map p₁) (F.map p₂) hf₁ hf₂ hd z hz
  exact FlatCycle.Construction.FlatCycleDetection.exists_cycle D.f.hom
    (TensorProduct.mk A (IsLocalRing.ResidueField A) (A ⊗[R] D.X₁) 1) x hx
    (fun h => hne (he.symm.trans h))

end Construction.FlatTwoAxisCycleLift

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.TwoAxisCycleLift
