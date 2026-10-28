import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.AdelicCharacter
import OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData

/-! # Finite Operators -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.FiniteOperators.CM.Sections

/-! Real and finite sections of actual adelic Schwartz functions.
Their membership is derived from the defining finite tensor span. -/

open scoped Classical
open OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction
variable {I : Type*} [Fintype I]

def join (x : I → ℝ) (y : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ := fun i => (x i, y i)

theorem realSection_mem (y : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (F : (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) → ℂ) (hF : F ∈ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I) :
    (fun x => F (join x y)) ∈ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨f, φ, rfl⟩ := hF
    have he : (fun x => RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.pureTensor f φ (join x y)) = (φ.val y) • f.val := by
      funext x
      exact mul_comm (f.val x) (φ.val y)
    rw [he]
    exact (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I).smul_mem _ f.property
  | zero => exact (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I).zero_mem
  | add F G _ _ hF hG => exact (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I).add_mem hF hG
  | smul c F _ hF => exact (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I).smul_mem c hF

theorem finiteSection_mem (x : I → ℝ) (F : (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) → ℂ) (hF : F ∈ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I) :
    (fun y => F (join x y)) ∈ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨f, φ, rfl⟩ := hF
    exact (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I).smul_mem (f.val x) φ.property
  | zero => exact (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I).zero_mem
  | add F G _ _ hF hG => exact (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I).add_mem hF hG
  | smul c F _ hF => exact (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I).smul_mem c hF

def realSection (y : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I →ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I where
  toFun F := ⟨fun x => F.val (join x y), realSection_mem y F.val F.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def finiteSection (x : I → ℝ) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I →ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I where
  toFun F := ⟨fun y => F.val (join x y), finiteSection_mem x F.val F.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem realSection_tensor (y : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) :
    realSection y (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor f φ) = (φ.val y) • f := by
  apply Subtype.ext
  funext x
  exact mul_comm (f.val x) (φ.val y)

theorem finiteSection_tensor (x : I → ℝ) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) :
    finiteSection x (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor f φ) = (f.val x) • φ := rfl

theorem linear_ext {M : Type*} [AddCommMonoid M] [Module ℂ M]
    (U V : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I →ₗ[ℂ] M)
    (h : ∀ (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I), U (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor f φ) = V (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor f φ)) : U = V := by
  apply LinearMap.ext
  intro F
  obtain ⟨F, hF⟩ := F
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨f, φ, rfl⟩ := hF
    exact h f φ
  | zero => exact U.map_zero.trans V.map_zero.symm
  | add F G hF hG ihF ihG =>
    change U (⟨F, hF⟩ + ⟨G, hG⟩) = V (⟨F, hF⟩ + ⟨G, hG⟩)
    rw [map_add, map_add, ihF, ihG]
  | smul c F hF ih =>
    change U (c • ⟨F, hF⟩) = V (c • ⟨F, hF⟩)
    rw [map_smul, map_smul, ih]

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.FiniteOperators.CM.Sections

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.FiniteOperators.CM

/-! Extend an actual finite Schwartz operator to adelic Schwartz
functions by applying it to each finite section. -/

open scoped Classical
open OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.FiniteOperators.CM.Sections
variable {I : Type*} [Fintype I]

def raw (U : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I →ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I →ₗ[ℂ] ((I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) → ℂ) where
  toFun F x := (U (Sections.finiteSection (fun i => (x i).1) F)).val (fun i => (x i).2)
  map_add' F G := by
    funext x
    rw [map_add, map_add]
    rfl
  map_smul' c F := by
    funext x
    rw [map_smul, map_smul]
    rfl

theorem raw_tensor (U : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I →ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I)
    (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) : raw U (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor f φ) = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.pureTensor f (U φ) := by
  funext x
  change (U (Sections.finiteSection (fun i => (x i).1) (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor f φ))).val (fun i => (x i).2) = _
  rw [Sections.finiteSection_tensor, map_smul]
  rfl

theorem raw_mem (U : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I →ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (F : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I) :
    raw U F ∈ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I := by
  obtain ⟨F, hF⟩ := F
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨f, φ, rfl⟩ := hF
    change raw U (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor f φ) ∈ _
    rw [raw_tensor]
    exact (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor f (U φ)).property
  | zero =>
    change raw U 0 ∈ _
    rw [map_zero]
    exact (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I).zero_mem
  | add F G hF hG ihF ihG =>
    change raw U (⟨F, hF⟩ + ⟨G, hG⟩) ∈ _
    rw [map_add]
    exact (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I).add_mem ihF ihG
  | smul c F hF ih =>
    change raw U (c • ⟨F, hF⟩) ∈ _
    rw [map_smul]
    exact (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I).smul_mem c ih

def extend (U : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I →ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I →ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I :=
  (raw U).codRestrict (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I) (raw_mem U)

theorem extend_tensor (U : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I →ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I)
    (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) : extend U (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor f φ) = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor f (U φ) :=
  Subtype.ext (raw_tensor U f φ)

theorem extend_id : extend (LinearMap.id (R := ℂ) (M := RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I)) = LinearMap.id := by
  apply Sections.linear_ext
  intro f φ
  rw [extend_tensor]
  rfl

theorem extend_comp (U V : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I →ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) :
    extend (U.comp V) = (extend U).comp (extend V) := by
  apply Sections.linear_ext
  intro f φ
  simp only [LinearMap.comp_apply, extend_tensor]

def operator : (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) →*
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I) where
  toFun U := {
    toLinearMap := extend U.toLinearMap
    invFun := extend U.symm.toLinearMap
    left_inv F := by
      have h := congrArg (fun T : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I →ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I => T F)
        (extend_comp U.symm.toLinearMap U.toLinearMap).symm
      change extend U.symm.toLinearMap (extend U.toLinearMap F) = _ at h
      have hi : U.symm.toLinearMap.comp U.toLinearMap = LinearMap.id := by
        apply LinearMap.ext
        exact U.symm_apply_apply
      rw [hi, extend_id] at h
      exact h
    right_inv F := by
      have h := congrArg (fun T : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I →ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I => T F)
        (extend_comp U.toLinearMap U.symm.toLinearMap).symm
      change extend U.toLinearMap (extend U.symm.toLinearMap F) = _ at h
      have hi : U.toLinearMap.comp U.symm.toLinearMap = LinearMap.id := by
        apply LinearMap.ext
        exact U.apply_symm_apply
      rw [hi, extend_id] at h
      exact h }
  map_one' := by
    apply LinearEquiv.toLinearMap_injective
    exact extend_id
  map_mul' U V := by
    apply LinearEquiv.toLinearMap_injective
    exact extend_comp U.toLinearMap V.toLinearMap

theorem operator_tensor (U : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I)
    (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) : operator U (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor f φ) = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor f (U φ) :=
  extend_tensor U.toLinearMap f φ

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.FiniteOperators.CM

end

end OAI
