import OAI.NumberTheory.PadicHodge.IntegralComparison.DualTransportNaturality
import Mathlib.Algebra.Module.Equiv.Basic

/-! # Serre Unit Trace -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SerreUnitTrace

noncomputable section

/-! Evaluation of a Serre pairing at the actual unit class defines the
normalized trace. It is an isomorphism when that unit identifies the
coefficient ring with degree-zero cohomology, and it is natural for maps
which preserve the unit. -/

open _root_.CategoryTheory

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.DualHomologyTransport

variable (R : Type u) [CommRing R]

def evaluation (V : ModuleCat.{u} R) (v : V) : DualHomologyTransport.dualGroup R V ⟶ AddCommGrpCat.of R :=
  AddCommGrpCat.ofHom (Module.Dual.eval R V v).toAddMonoidHom

def evaluationIso {V : ModuleCat.{u} R} (e : R ≃ₗ[R] V) : DualHomologyTransport.dualGroup R V ≅ AddCommGrpCat.of R :=
  (e.dualMap.trans (LinearMap.ringLmapEquivSelf R R R)).toAddEquiv.toAddCommGrpIso

@[simp]
theorem evaluationIso_hom {V : ModuleCat.{u} R} (e : R ≃ₗ[R] V) :
    (evaluationIso R e).hom = evaluation R V (e 1) := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro φ
  rfl

@[reassoc]
theorem dualMap_evaluation {V W : ModuleCat.{u} R} (b : V ⟶ W) (v : V) :
    DualTransportNaturality.dualMap R b ≫ evaluation R V v = evaluation R W (b v) := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro φ
  rfl

def trace {A : AddCommGrpCat.{u}} {V : ModuleCat.{u} R} (p : A ≅ DualHomologyTransport.dualGroup R V) (v : V) :
    A ⟶ AddCommGrpCat.of R := p.hom ≫ evaluation R V v

def traceIso {A : AddCommGrpCat.{u}} {V : ModuleCat.{u} R}
    (p : A ≅ DualHomologyTransport.dualGroup R V) (e : R ≃ₗ[R] V) : A ≅ AddCommGrpCat.of R :=
  p ≪≫ evaluationIso R e

@[simp]
theorem traceIso_hom {A : AddCommGrpCat.{u}} {V : ModuleCat.{u} R}
    (p : A ≅ DualHomologyTransport.dualGroup R V) (e : R ≃ₗ[R] V) :
    (traceIso R p e).hom = trace R p (e 1) := by
  simp only [traceIso, Iso.trans_hom, evaluationIso_hom, trace]

theorem trace_isIso {A : AddCommGrpCat.{u}} {V : ModuleCat.{u} R}
    (p : A ≅ DualHomologyTransport.dualGroup R V) (v : V) (e : R ≃ₗ[R] V) (hv : e 1 = v) :
    IsIso (trace R p v) := by
  rw [← hv, ← traceIso_hom]
  infer_instance

@[reassoc]
theorem naturality {A₁ A₂ : AddCommGrpCat.{u}} {V₁ V₂ : ModuleCat.{u} R}
    (p₁ : A₁ ≅ DualHomologyTransport.dualGroup R V₁) (p₂ : A₂ ≅ DualHomologyTransport.dualGroup R V₂)
    (a : A₂ ⟶ A₁) (b : V₁ ⟶ V₂) (v₁ : V₁) (v₂ : V₂)
    (hp : a ≫ p₁.hom = p₂.hom ≫ DualTransportNaturality.dualMap R b)
    (hv : b v₁ = v₂) : a ≫ trace R p₁ v₁ = trace R p₂ v₂ := by
  rw [trace, ← Category.assoc, hp, Category.assoc, dualMap_evaluation, hv]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SerreUnitTrace
