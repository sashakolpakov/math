import OAI.RepresentationTheory.Theta.Geometric.TangentAddition
import OAI.RepresentationTheory.Theta.Geometric.LieFieldTests
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Lie Rank -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRank.LieRankLinearTransport

noncomputable section

/-! A complex-linear equivalence intertwining the actual native
differentials transports the original Lie-rank condition over every
extended test field. All tangent points are genuine dual-number points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct _root_.CategoryTheory.MonObj

variable {R : Type} [CommRing R] {g : ℕ}
    (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase) (ρ : ActionData.IntegralAction R A)

local instance : IsIntegral A.scheme.left := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.carrier_integral A

variable (F : Type) [Field F] [Algebra ℂ F] (τ : R →+* F)

def geometricEigenSpace : Submodule F (F ⊗[ℂ] RepresentationTheory.Theta.Geometric.GroupDerivative.nativeTangentModel A.scheme) where
  carrier := {v | ∀ a, RepresentationTheory.Theta.Geometric.TangentAddition.geometricGroupDerivative F (ρ.map a) v = τ a • v}
  zero_mem' a := by rw [map_zero, smul_zero]
  add_mem' hv hw a := by rw [map_add, hv a, hw a, smul_add]
  smul_mem' c v hv a := by rw [map_smul, hv a, smul_comm]

def chart : RepresentationTheory.Theta.Geometric.Intrinsic.TangentCharts.NativeTangentChart A.scheme 1 := RepresentationTheory.Theta.Geometric.Intrinsic.TangentCharts.nativeTangentChart A.scheme 1

theorem geometricEigenpoint_iff (v : F ⊗[ℂ] RepresentationTheory.Theta.Geometric.GroupDerivative.nativeTangentModel A.scheme) :
    (∀ a, ((chart A).geometricTangentEquiv F v).val ≫ ρ.map a =
      RepresentationTheory.Theta.Geometric.LieFieldTests.extendedDualScalar ℂ F (τ a) ≫ ((chart A).geometricTangentEquiv F v).val) ↔
        v ∈ geometricEigenSpace A ρ F τ := by
  constructor
  · intro h a
    apply ((chart A).geometricTangentEquiv F).injective
    apply Subtype.ext
    exact ((chart A).geometricGroup_naturality F (chart A) (ρ.map a) v).trans
      ((h a).trans ((chart A).geometricTangentEquiv_smul F (τ a) v).symm)
  · intro h a
    exact ((chart A).geometricGroup_naturality F (chart A) (ρ.map a) v).symm.trans
      ((congrArg (fun w => ((chart A).geometricTangentEquiv F w).val) (h a)).trans
        ((chart A).geometricTangentEquiv_smul F (τ a) v))

def geometricEigenEquiv : geometricEigenSpace A ρ F τ ≃ RepresentationTheory.Theta.Geometric.LieFieldTests.extendedLieEigenpoints ℂ F A ρ τ where
  toFun v := ⟨((chart A).geometricTangentEquiv F v.val).val,
    (((chart A).geometricTangentEquiv F v.val).property).trans (MonObj.comp_one _),
    (geometricEigenpoint_iff A ρ F τ v.val).mpr v.property⟩
  invFun t := ⟨((chart A).geometricTangentEquiv F).symm
    ⟨t.val, t.property.1.trans (MonObj.comp_one _).symm⟩, by
      apply (geometricEigenpoint_iff A ρ F τ _).mp
      have he := congrArg Subtype.val (((chart A).geometricTangentEquiv F).apply_symm_apply
        ⟨t.val, t.property.1.trans (MonObj.comp_one _).symm⟩)
      intro a
      exact (congrArg (fun z => z ≫ ρ.map a) he).trans
        ((t.property.2 a).trans (congrArg (fun z => RepresentationTheory.Theta.Geometric.LieFieldTests.extendedDualScalar ℂ F (τ a) ≫ z) he).symm)⟩
  left_inv v := Subtype.ext (((chart A).geometricTangentEquiv F).symm_apply_apply v.val)
  right_inv t := by
    apply Subtype.ext
    exact congrArg (fun z : RepresentationTheory.Theta.Geometric.TangentSources.extendedSchemeTangentPoints ℂ F A.scheme (RepresentationTheory.Theta.Geometric.ExtendedComplexPoints.extendedComplexPoint F 1) => z.val)
      (((chart A).geometricTangentEquiv F).apply_symm_apply
        ⟨t.val, t.property.1.trans (MonObj.comp_one _).symm⟩)

theorem geometricEigenEquiv_add (v w : geometricEigenSpace A ρ F τ) :
    (geometricEigenEquiv A ρ F τ (v + w)).val =
      (geometricEigenEquiv A ρ F τ v).val * (geometricEigenEquiv A ρ F τ w).val :=
  (chart A).geometricTangentEquiv_add F v.val w.val

theorem geometricEigenEquiv_smul (c : F) (v : geometricEigenSpace A ρ F τ) :
    (geometricEigenEquiv A ρ F τ (c • v)).val =
      RepresentationTheory.Theta.Geometric.LieFieldTests.extendedDualScalar ℂ F c ≫ (geometricEigenEquiv A ρ F τ v).val :=
  (chart A).geometricTangentEquiv_smul F c v.val

theorem hasLieRank_iff_geometricEigen_finrank (r : ℕ) :
    LieRanks.HasLieRank (A.pullback (RepresentationTheory.Theta.Geometric.LieFieldTests.fieldBaseMap ℂ F)) (ρ.pullback (RepresentationTheory.Theta.Geometric.LieFieldTests.fieldBaseMap ℂ F)) τ r ↔
      Module.finrank F (geometricEigenSpace A ρ F τ) = r := by
  constructor
  · rintro ⟨e, hadd, hscalar⟩
    let d := e.trans ((RepresentationTheory.Theta.Geometric.LieFieldTests.lieFieldTestEquiv ℂ F A ρ τ).trans (geometricEigenEquiv A ρ F τ).symm)
    have hd (v : Fin r → F) : geometricEigenEquiv A ρ F τ (d v) =
        RepresentationTheory.Theta.Geometric.LieFieldTests.lieFieldTestEquiv ℂ F A ρ τ (e v) := by
      exact (geometricEigenEquiv A ρ F τ).apply_symm_apply _
    have hda (v w : Fin r → F) : d (v + w) = d v + d w := by
      apply (geometricEigenEquiv A ρ F τ).injective
      apply Subtype.ext
      exact (congrArg (fun z : RepresentationTheory.Theta.Geometric.LieFieldTests.extendedLieEigenpoints ℂ F A ρ τ => z.val) (hd (v + w))).trans
        ((RepresentationTheory.Theta.Geometric.LieFieldTests.lieFieldTestEquiv_mul ℂ F A ρ τ (e v) (e w) (e (v + w)) (hadd v w)).trans
          ((congrArg₂ (fun z w : RepresentationTheory.Theta.Geometric.LieFieldTests.extendedLieEigenpoints ℂ F A ρ τ => z.val * w.val)
            (hd v).symm (hd w).symm).trans (geometricEigenEquiv_add A ρ F τ (d v) (d w)).symm))
    have hds (c : F) (v : Fin r → F) : d (c • v) = c • d v := by
      apply (geometricEigenEquiv A ρ F τ).injective
      apply Subtype.ext
      exact (congrArg (fun z : RepresentationTheory.Theta.Geometric.LieFieldTests.extendedLieEigenpoints ℂ F A ρ τ => z.val) (hd (c • v))).trans
        ((RepresentationTheory.Theta.Geometric.LieFieldTests.lieFieldTestEquiv_scalar ℂ F A ρ τ c (e v) (e (c • v)) (hscalar c v)).trans
          ((congrArg (fun z : RepresentationTheory.Theta.Geometric.LieFieldTests.extendedLieEigenpoints ℂ F A ρ τ =>
            RepresentationTheory.Theta.Geometric.LieFieldTests.extendedDualScalar ℂ F c ≫ z.val) (hd v).symm).trans
              (geometricEigenEquiv_smul A ρ F τ c (d v)).symm))
    let l : (Fin r → F) ≃ₗ[F] geometricEigenSpace A ρ F τ := {
      toEquiv := d
      map_add' := hda
      map_smul' := hds }
    simpa only [Module.finrank_fin_fun] using l.finrank_eq.symm
  · intro hr
    let : Module.Free F (geometricEigenSpace A ρ F τ) :=
      Module.Free.of_divisionRing F (geometricEigenSpace A ρ F τ)
    let b := (Module.finBasis F (geometricEigenSpace A ρ F τ)).reindex (finCongr hr)
    let e := b.equivFun.symm
    apply RepresentationTheory.Theta.Geometric.LieFieldTests.hasLieRank_of_extended ℂ F A ρ τ r (e.toEquiv.trans (geometricEigenEquiv A ρ F τ))
    · intro v w
      change (geometricEigenEquiv A ρ F τ (e (v + w))).val = _
      rw [map_add, geometricEigenEquiv_add]
      rfl
    · intro c v
      change (geometricEigenEquiv A ρ F τ (e (c • v))).val = _
      rw [map_smul, geometricEigenEquiv_smul]
      rfl

section Transport

variable (B : HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase) (σ : ActionData.IntegralAction R B)
local instance : IsIntegral B.scheme.left := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.carrier_integral B

variable (e : RepresentationTheory.Theta.Geometric.GroupDerivative.nativeTangentModel A.scheme ≃ₗ[ℂ] RepresentationTheory.Theta.Geometric.GroupDerivative.nativeTangentModel B.scheme)
    (he : ∀ a v, RepresentationTheory.Theta.Geometric.GroupDerivative.nativeGroupDerivative (σ.map a) (e v) = e (RepresentationTheory.Theta.Geometric.GroupDerivative.nativeGroupDerivative (ρ.map a) v))

include he in
theorem baseChange_intertwines (a : R) (v : F ⊗[ℂ] RepresentationTheory.Theta.Geometric.GroupDerivative.nativeTangentModel A.scheme) :
    RepresentationTheory.Theta.Geometric.TangentAddition.geometricGroupDerivative F (σ.map a) (e.baseChange ℂ F _ _ v) =
      e.baseChange ℂ F _ _ (RepresentationTheory.Theta.Geometric.TangentAddition.geometricGroupDerivative F (ρ.map a) v) := by
  induction v using TensorProduct.inductionOn with
  | add v w hv hw => simp only [map_add, hv, hw]
  | tmul c v => exact congrArg (fun w => c ⊗ₜ[ℂ] w) (he a v)

def geometricEigenTransport :
    geometricEigenSpace A ρ F τ ≃ₗ[F] geometricEigenSpace B σ F τ where
  toFun v := ⟨e.baseChange ℂ F _ _ v.val, by
    intro a
    rw [baseChange_intertwines A ρ F B σ e he, v.property a, map_smul]⟩
  invFun w := ⟨(e.baseChange ℂ F _ _).symm w.val, by
    intro a
    apply (e.baseChange ℂ F _ _).injective
    rw [← baseChange_intertwines A ρ F B σ e he, LinearEquiv.apply_symm_apply,
      w.property a, map_smul, LinearEquiv.apply_symm_apply]⟩
  left_inv v := Subtype.ext ((e.baseChange ℂ F _ _).symm_apply_apply v.val)
  right_inv w := Subtype.ext ((e.baseChange ℂ F _ _).apply_symm_apply w.val)
  map_add' v w := Subtype.ext ((e.baseChange ℂ F _ _).map_add v.val w.val)
  map_smul' c v := Subtype.ext ((e.baseChange ℂ F _ _).map_smul c v.val)

include he in
theorem hasLieRank_fieldBaseMap (r : ℕ)
    (hr : LieRanks.HasLieRank (A.pullback (RepresentationTheory.Theta.Geometric.LieFieldTests.fieldBaseMap ℂ F)) (ρ.pullback (RepresentationTheory.Theta.Geometric.LieFieldTests.fieldBaseMap ℂ F)) τ r) :
    LieRanks.HasLieRank (B.pullback (RepresentationTheory.Theta.Geometric.LieFieldTests.fieldBaseMap ℂ F)) (σ.pullback (RepresentationTheory.Theta.Geometric.LieFieldTests.fieldBaseMap ℂ F)) τ r := by
  apply (hasLieRank_iff_geometricEigen_finrank B σ F τ r).mpr
  exact (geometricEigenTransport A ρ F τ B σ e he).finrank_eq.symm.trans
    ((hasLieRank_iff_geometricEigen_finrank A ρ F τ r).mp hr)

end Transport

variable (B : HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase) (σ : ActionData.IntegralAction R B)
local instance : IsIntegral B.scheme.left := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.carrier_integral B

theorem hasLieRank_after_baseChange
    (e : RepresentationTheory.Theta.Geometric.GroupDerivative.nativeTangentModel A.scheme ≃ₗ[ℂ] RepresentationTheory.Theta.Geometric.GroupDerivative.nativeTangentModel B.scheme)
    (he : ∀ a v, RepresentationTheory.Theta.Geometric.GroupDerivative.nativeGroupDerivative (σ.map a) (e v) = e (RepresentationTheory.Theta.Geometric.GroupDerivative.nativeGroupDerivative (ρ.map a) v))
    (k : Type) [Field k] (p : Spec (.of k) ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (τk : R →+* k) (r : ℕ)
    (hr : LieRanks.HasLieRank (A.pullback p) (ρ.pullback p) τk r) :
    LieRanks.HasLieRank (B.pullback p) (σ.pullback p) τk r := by
  let jfield : ℂ →+* k := (Spec.preimage p).hom
  let : Algebra ℂ k := jfield.toAlgebra
  have hp : RepresentationTheory.Theta.Geometric.LieFieldTests.fieldBaseMap ℂ k = p := Spec.map_preimage p
  rw [← hp] at hr ⊢
  exact hasLieRank_fieldBaseMap A ρ k τk B σ e he r hr

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRank.LieRankLinearTransport
