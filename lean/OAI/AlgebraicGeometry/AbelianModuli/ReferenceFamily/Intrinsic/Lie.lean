import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SchemeDualAddition
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter

/-! # Lie -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Lie

/-! The original dual-number Lie eigenpoints are precisely the
eigenspaces of the actual native complex manifold differentials. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

variable {R : Type} [CommRing R] {g : ℕ}
    (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase) (ρ : ActionData.IntegralAction R A) (τ : R →+* ℂ)

local instance : IsIntegral A.scheme.left := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.carrier_integral A
local notation "ModelA" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.scheme.hom) → ℂ)

def nativeLieDifferential (a : R) : ModelA →ₗ[ℂ] ModelA :=
  (mfderiv 𝓘(ℂ, ModelA) 𝓘(ℂ, ModelA) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ρ.map a)) 1).toLinearMap

def nativeLieEigenspace : Submodule ℂ ModelA where
  carrier := {v | ∀ a : R, nativeLieDifferential A ρ a v = τ a • v}
  zero_mem' a := by rw [map_zero, smul_zero]
  add_mem' hu hv a := by rw [map_add, hu a, hv a, smul_add]
  smul_mem' z v hv a := by rw [map_smul, hv a, smul_comm]

theorem nativeSchemeTangentDual_action (a : R) (v : ModelA) :
    (SchemeDualTangent.nativeSchemeTangentDualEquiv A.scheme 1
      (mfderiv 𝓘(ℂ, ModelA) 𝓘(ℂ, ModelA) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ρ.map a)) 1 v)).val =
      (SchemeDualTangent.nativeSchemeTangentDualEquiv A.scheme 1 v).val ≫ ρ.map a := by
  have hn := SchemeDualNaturality.nativeSchemeTangentDual_natural (ρ.map a) 1 v
  have hp : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ρ.map a) 1 = (1 : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.scheme) :=
    MonObj.one_comp (ρ.map a)
  have he := congrArg (fun p => (SchemeDualTangent.nativeSchemeTangentDualEquiv A.scheme p
    (mfderiv 𝓘(ℂ, ModelA) 𝓘(ℂ, ModelA) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ρ.map a)) 1 v)).val) hp
  exact he.symm.trans hn

theorem nativeLieEigenpoint_iff (v : ModelA) :
    (∀ a : R, (SchemeDualTangent.nativeSchemeTangentDualEquiv A.scheme 1 v).val ≫ ρ.map a =
      LieRanks.dualNumberScalar ℂ (τ a) ≫ (SchemeDualTangent.nativeSchemeTangentDualEquiv A.scheme 1 v).val) ↔
      v ∈ nativeLieEigenspace A ρ τ := by
  constructor
  · intro h a
    apply (SchemeDualTangent.nativeSchemeTangentDualEquiv A.scheme 1).injective
    apply Subtype.ext
    exact (nativeSchemeTangentDual_action A ρ a v).trans
      ((h a).trans (SchemeDualNaturality.nativeSchemeTangentDual_scale A.scheme 1 (τ a) v).symm)
  · intro h a
    exact (nativeSchemeTangentDual_action A ρ a v).symm.trans
      ((congrArg (fun w : ModelA => (SchemeDualTangent.nativeSchemeTangentDualEquiv A.scheme 1 w).val) (h a)).trans
        (SchemeDualNaturality.nativeSchemeTangentDual_scale A.scheme 1 (τ a) v))

def nativeLieEigenpointsEquiv : nativeLieEigenspace A ρ τ ≃ LieRanks.LieEigenpoints A ρ τ where
  toFun v := ⟨(SchemeDualTangent.nativeSchemeTangentDualEquiv A.scheme 1 v.val).val,
    (SchemeDualTangent.nativeSchemeTangentDualEquiv A.scheme 1 v.val).property,
    (nativeLieEigenpoint_iff A ρ τ v.val).mpr v.property⟩
  invFun f := ⟨(SchemeDualTangent.nativeSchemeTangentDualEquiv A.scheme 1).symm ⟨f.val, f.property.1⟩, by
    apply (nativeLieEigenpoint_iff A ρ τ _).mp
    have he := congrArg Subtype.val
      ((SchemeDualTangent.nativeSchemeTangentDualEquiv A.scheme 1).apply_symm_apply ⟨f.val, f.property.1⟩)
    intro a
    exact (congrArg (fun l => l ≫ ρ.map a) he).trans
      ((f.property.2 a).trans (congrArg (fun l => LieRanks.dualNumberScalar ℂ (τ a) ≫ l) he).symm)⟩
  left_inv v := Subtype.ext ((SchemeDualTangent.nativeSchemeTangentDualEquiv A.scheme 1).symm_apply_apply v.val)
  right_inv f := Subtype.ext (congrArg (fun q : DualOpen.Lifts.DualSchemePoints A.scheme 1 => q.val)
    ((SchemeDualTangent.nativeSchemeTangentDualEquiv A.scheme 1).apply_symm_apply ⟨f.val, f.property.1⟩))

theorem nativeLieEigenpointsEquiv_add (u v : nativeLieEigenspace A ρ τ) :
    (nativeLieEigenpointsEquiv A ρ τ (u + v)).val =
      (nativeLieEigenpointsEquiv A ρ τ u).val * (nativeLieEigenpointsEquiv A ρ τ v).val :=
  SchemeDualAddition.nativeSchemeTangentDual_add A.scheme u.val v.val

theorem nativeLieEigenpointsEquiv_smul (a : ℂ) (v : nativeLieEigenspace A ρ τ) :
    (nativeLieEigenpointsEquiv A ρ τ (a • v)).val =
      LieRanks.dualNumberScalar ℂ a ≫ (nativeLieEigenpointsEquiv A ρ τ v).val :=
  SchemeDualNaturality.nativeSchemeTangentDual_scale A.scheme 1 a v.val

end AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Lie

namespace AlgebraicGeometry.AbelianModuli.ReferenceFamily
open _root_.CategoryTheory
open _root_.AlgebraicGeometry
open scoped _root_.Manifold
open scoped _root_.CategoryTheory.MonObj
section

/-! The original dual-number rank condition computes the dimension of
the actual native analytic tangent eigenspace. -/

open scoped ContDiff

variable {R : Type} [CommRing R] {g : ℕ}
    (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase) (ρ : ActionData.IntegralAction R A) (τ : R →+* ℂ)

theorem LieRanks.HasLieRank.native_finrank {r : ℕ} (hr : LieRanks.HasLieRank A ρ τ r) :
    Module.finrank ℂ (Intrinsic.Lie.nativeLieEigenspace A ρ τ) = r := by
  obtain ⟨e, hadd, hsmul⟩ := hr
  let d := Intrinsic.Lie.nativeLieEigenpointsEquiv A ρ τ
  let h : (Fin r → ℂ) ≃ Intrinsic.Lie.nativeLieEigenspace A ρ τ := e.trans d.symm
  have hh (x : Fin r → ℂ) : d (h x) = e x := d.apply_symm_apply (e x)
  let L : (Fin r → ℂ) ≃ₗ[ℂ] Intrinsic.Lie.nativeLieEigenspace A ρ τ :=
    { h with
      map_add' := by
        intro x y
        apply d.injective
        apply Subtype.ext
        exact (congrArg Subtype.val (hh (x + y))).trans
          ((hadd x y).trans
            ((congrArg₂ (· * ·) (congrArg Subtype.val (hh x))
              (congrArg Subtype.val (hh y))).symm.trans
              (Intrinsic.Lie.nativeLieEigenpointsEquiv_add A ρ τ (h x) (h y)).symm))
      map_smul' := by
        intro a x
        apply d.injective
        apply Subtype.ext
        exact (congrArg Subtype.val (hh (a • x))).trans
          ((hsmul a x).trans
            ((congrArg (fun f => LieRanks.dualNumberScalar ℂ a ≫ f) (congrArg Subtype.val (hh x))).symm.trans
              (Intrinsic.Lie.nativeLieEigenpointsEquiv_smul A ρ τ a (h x)).symm)) }
  exact L.finrank_eq.symm.trans (Module.finrank_fin_fun ℂ)

end

/-! Native tangent eigenspace dimensions are equivalent to the original
dual-number Lie rank condition, including addition and scalar action. -/

variable {R : Type} [CommRing R] {g : ℕ}
    (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase) (ρ : ActionData.IntegralAction R A) (τ : R →+* ℂ)

theorem LieRanks.HasLieRank.of_native_finrank {r : ℕ}
    (hr : Module.finrank ℂ (Intrinsic.Lie.nativeLieEigenspace A ρ τ) = r) : LieRanks.HasLieRank A ρ τ r := by
  let b := (Module.finBasis ℂ (Intrinsic.Lie.nativeLieEigenspace A ρ τ)).reindex (finCongr hr)
  let e := b.equivFun.symm
  refine ⟨e.toEquiv.trans (Intrinsic.Lie.nativeLieEigenpointsEquiv A ρ τ), ?_, ?_⟩
  · intro v w
    change (Intrinsic.Lie.nativeLieEigenpointsEquiv A ρ τ (e (v + w))).val = _
    rw [map_add, Intrinsic.Lie.nativeLieEigenpointsEquiv_add]
    rfl
  · intro c v
    change (Intrinsic.Lie.nativeLieEigenpointsEquiv A ρ τ (e (c • v))).val = _
    rw [map_smul, Intrinsic.Lie.nativeLieEigenpointsEquiv_smul]
    rfl

theorem Intrinsic.Lie.hasLieRank_iff_native_finrank (r : ℕ) : LieRanks.HasLieRank A ρ τ r ↔
    Module.finrank ℂ (Intrinsic.Lie.nativeLieEigenspace A ρ τ) = r :=
  ⟨fun h => h.native_finrank A ρ τ, LieRanks.HasLieRank.of_native_finrank A ρ τ⟩

end AlgebraicGeometry.AbelianModuli.ReferenceFamily

end

end OAI
