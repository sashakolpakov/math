import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LieAlgebraic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Lie Eigenspaces -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.LieEigenspaces

noncomputable section

/-! ReferenceFamily's literal Lie eigenpoints agree with algebraic eigenspaces
of the constructed differential action over any field. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

namespace AlgebraicLie

variable {k R : Type} [Field k] [CommRing R] {g : ℕ}
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A) (τ : R →+* k)

def eigenspace : Submodule k (LiePoints.AlgebraicLie.Space A.scheme) :=
  ⨅ a : R, LinearMap.ker (LieAlgebraic.AlgebraicLie.action A ρ a - τ a • LinearMap.id)

theorem mem_eigenspace_iff (v : LiePoints.AlgebraicLie.Space A.scheme) :
    v ∈ eigenspace A ρ τ ↔ ∀ a : R, LieAlgebraic.AlgebraicLie.action A ρ a v = τ a • v := by
  simp only [eigenspace, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

theorem eigenpoint_iff (v : LiePoints.AlgebraicLie.Space A.scheme) :
    (∀ a : R, LiePoints.AlgebraicLie.point A.scheme v ≫ ρ.map a =
      AbelianModuli.ReferenceFamily.LieRanks.dualNumberScalar k (τ a) ≫ LiePoints.AlgebraicLie.point A.scheme v) ↔ v ∈ eigenspace A ρ τ := by
  rw [mem_eigenspace_iff]
  constructor
  · intro h a
    rw [LieAlgebraic.AlgebraicLie.action_apply]
    apply LiePoints.AlgebraicLie.point_injective A.scheme
    exact (LieAlgebraic.AlgebraicLie.point_map (ρ.map a) v).trans ((h a).trans (LieAlgebraic.AlgebraicLie.point_smul A.scheme (τ a) v).symm)
  · intro h a
    have hv := h a
    rw [LieAlgebraic.AlgebraicLie.action_apply] at hv
    exact (LieAlgebraic.AlgebraicLie.point_map (ρ.map a) v).symm.trans
      ((congrArg (LiePoints.AlgebraicLie.point A.scheme) hv).trans (LieAlgebraic.AlgebraicLie.point_smul A.scheme (τ a) v))

def eigenpointsEquiv : eigenspace A ρ τ ≃ AbelianModuli.ReferenceFamily.LieRanks.LieEigenpoints A ρ τ where
  toFun v := ⟨LiePoints.AlgebraicLie.point A.scheme v.val, LiePoints.AlgebraicLie.point_origin A.scheme v.val, (eigenpoint_iff A ρ τ v.val).mpr v.property⟩
  invFun x := ⟨(LiePoints.AlgebraicLie.pointsEquiv A.scheme).symm ⟨x.val, x.property.1⟩, by
    apply (eigenpoint_iff A ρ τ _).mp
    have he := congrArg Subtype.val ((LiePoints.AlgebraicLie.pointsEquiv A.scheme).apply_symm_apply ⟨x.val, x.property.1⟩)
    change LiePoints.AlgebraicLie.point A.scheme ((LiePoints.AlgebraicLie.pointsEquiv A.scheme).symm ⟨x.val, x.property.1⟩) = x.val at he
    rw [he]
    exact x.property.2⟩
  left_inv v := Subtype.ext ((LiePoints.AlgebraicLie.pointsEquiv A.scheme).symm_apply_apply v.val)
  right_inv x := by
    apply Subtype.ext
    have h := (LiePoints.AlgebraicLie.pointsEquiv A.scheme).apply_symm_apply ⟨x.val, x.property.1⟩
    exact congrArg (fun q : {f : AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest k ⟶ A.scheme //
      AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin k ≫ f = 1} => q.val) h

theorem eigenpointsEquiv_add (v w : eigenspace A ρ τ) :
    (eigenpointsEquiv A ρ τ (v + w)).val =
      (eigenpointsEquiv A ρ τ v).val * (eigenpointsEquiv A ρ τ w).val := LiePoints.AlgebraicLie.point_add A.scheme v.val w.val

theorem eigenpointsEquiv_smul (c : k) (v : eigenspace A ρ τ) :
    (eigenpointsEquiv A ρ τ (c • v)).val =
      AbelianModuli.ReferenceFamily.LieRanks.dualNumberScalar k c ≫ (eigenpointsEquiv A ρ τ v).val := LieAlgebraic.AlgebraicLie.point_smul A.scheme c v.val

theorem hasLieRank_iff_linearEquiv (r : ℕ) :
    AbelianModuli.ReferenceFamily.LieRanks.HasLieRank A ρ τ r ↔ Nonempty ((Fin r → k) ≃ₗ[k] eigenspace A ρ τ) := by
  let d := eigenpointsEquiv A ρ τ
  constructor
  · rintro ⟨e, hadd, hsmul⟩
    let h := e.trans d.symm
    have hh (x : Fin r → k) : d (h x) = e x := d.apply_symm_apply (e x)
    refine ⟨{ h with map_add' := ?_, map_smul' := ?_ }⟩
    · intro x y
      apply d.injective
      apply Subtype.ext
      exact (congrArg Subtype.val (hh (x + y))).trans
        ((hadd x y).trans ((congrArg₂ (· * ·) (congrArg Subtype.val (hh x))
          (congrArg Subtype.val (hh y))).symm.trans (eigenpointsEquiv_add A ρ τ (h x) (h y)).symm))
    · intro c x
      apply d.injective
      apply Subtype.ext
      exact (congrArg Subtype.val (hh (c • x))).trans
        ((hsmul c x).trans ((congrArg (fun f => AbelianModuli.ReferenceFamily.LieRanks.dualNumberScalar k c ≫ f)
          (congrArg Subtype.val (hh x))).symm.trans (eigenpointsEquiv_smul A ρ τ c (h x)).symm))
  · rintro ⟨e⟩
    refine ⟨e.toEquiv.trans d, ?_, ?_⟩
    · intro x y
      change (d (e (x + y))).val = (d (e x)).val * (d (e y)).val
      rw [e.map_add]
      exact eigenpointsEquiv_add A ρ τ (e x) (e y)
    · intro c x
      change (d (e (c • x))).val = AbelianModuli.ReferenceFamily.LieRanks.dualNumberScalar k c ≫ (d (e x)).val
      rw [e.map_smul]
      exact eigenpointsEquiv_smul A ρ τ c (e x)

end AlgebraicLie

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.LieEigenspaces
