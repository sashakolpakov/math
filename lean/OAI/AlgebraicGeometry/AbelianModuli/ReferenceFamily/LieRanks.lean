import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData
import Mathlib.Algebra.DualNumber

/-! # Lie Ranks -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks

noncomputable section

/-! Lie eigenspaces are defined using actual dual-number points at the
identity. Rank means an additive, scalar-preserving coordinate bijection,
so no arbitrarily chosen vector-space structure on the point set is used. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u v

variable (k : Type u) [Field k]

def dualNumberTest : Over (Spec (.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))

def dualNumberReduction : DualNumber k →+* k :=
  (TrivSqZeroExt.fstHom k k k).toRingHom

def dualNumberOrigin : Over.mk (𝟙 (Spec (.of k))) ⟶ dualNumberTest k :=
  Over.homMk (Spec.map (CommRingCat.ofHom (dualNumberReduction k))) (by
    change Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp]
    have h : CommRingCat.ofHom (algebraMap k (DualNumber k)) ≫
        CommRingCat.ofHom (dualNumberReduction k) = 𝟙 (CommRingCat.of k) := by
      ext x
      rfl
    rw [h, Spec.map_id])

def dualNumberScale (a : k) : DualNumber k →ₐ[k] DualNumber k :=
  TrivSqZeroExt.map (a • (LinearMap.id : k →ₗ[k] k))

def dualNumberScalar (a : k) : dualNumberTest k ⟶ dualNumberTest k :=
  Over.homMk (Spec.map (CommRingCat.ofHom (dualNumberScale k a).toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact RingHom.ext (fun x => (dualNumberScale k a).commutes x))

variable {k} {R : Type v} [CommRing R] {g : ℕ}

/-- The eigenspace of the differential of the integral action at the
identity, defined on the actual scheme's dual-number test points. -/
def LieEigenpoints (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
    (ρ : ActionData.IntegralAction R A) (τ : R →+* k) :=
  {x : dualNumberTest k ⟶ A.scheme //
    dualNumberOrigin k ≫ x = 1 ∧
    ∀ a : R, x ≫ ρ.map a = dualNumberScalar k (τ a) ≫ x}

/-- An r-dimensional eigenspace, with its intrinsic pointwise addition
and dual-number scalar operations. The coordinate choice is existential. -/
def HasLieRank (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
    (ρ : ActionData.IntegralAction R A) (τ : R →+* k) (r : ℕ) : Prop :=
  ∃ e : (Fin r → k) ≃ LieEigenpoints A ρ τ,
    (∀ x y, (e (x + y)).val = (e x).val * (e y).val) ∧
    (∀ (a : k) x, (e (a • x)).val = dualNumberScalar k a ≫ (e x).val)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks
