import Mathlib.Data.Finset.NoncommProd
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-! # Commuting Product -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.CommutingProduct.CM

noncomputable section

/-! Finite products of commuting coordinate actions, and exact eventual
realization on each vector. The latter property is closed under the
group operations. -/

open scoped Classical

variable {V G : Type*} {L : V → Type*} [Group G] [∀ v, Group (L v)]
variable (φ : ∀ v, L v →* G)
variable (hc : Pairwise fun v w => ∀ a b, Commute (φ v a) (φ w b))

def product (S : Finset V) : (∀ v, L v) →* G where
  toFun a := S.noncommProd (fun v => φ v (a v)) (fun _ _ _ _ hvw => hc hvw _ _)
  map_one' := by
    exact (Finset.noncommProd_eq_pow_card S _ _ 1 (fun v _ => (φ v).map_one)).trans (one_pow _)
  map_mul' a b := by
    calc
      S.noncommProd (fun v => φ v ((a * b) v)) _ =
          S.noncommProd ((fun v => φ v (a v)) * (fun v => φ v (b v))) _ :=
        Finset.noncommProd_congr rfl (fun v _ => (φ v).map_mul _ _) _
      _ = _ := Finset.noncommProd_mul_distrib _ _ _ _ (fun _ _ _ _ hvw => hc hvw _ _)

theorem product_empty (a : ∀ v, L v) : product φ hc ∅ a = 1 := rfl

theorem product_insert (S : Finset V) (v : V) (hv : v ∉ S) (a : ∀ v, L v) :
    product φ hc (insert v S) a = φ v (a v) * product φ hc S a :=
  Finset.noncommProd_insert_of_notMem S v _ (fun _ _ _ _ hvw => hc hvw _ _) hv

variable {K M A : Type*} [Semiring K] [AddCommMonoid M] [Module K M] [Group A]
variable (Φ : ∀ _S : Finset V, (∀ v, L v) →* (M ≃ₗ[K] M))
variable (ρ : A →* (M ≃ₗ[K] M))
variable {P : V → Type*} [∀ v, Group (P v)]
variable (π : ∀ v, L v →* P v) (r : ∀ v, A →* P v)

def Realizes (a : A) : Prop := ∃ u : ∀ v, L v,
  (∀ v, π v (u v) = r v a) ∧
  ∀ f : M, ∃ S : Finset V, ∀ T : Finset V, S ⊆ T → Φ T u f = ρ a f

def realized : Subgroup A where
  carrier := Realizes Φ ρ π r
  one_mem' := by
    refine ⟨1, ?_, ?_⟩
    · intro v
      exact (π v).map_one.trans (r v).map_one.symm
    · intro f
      refine ⟨∅, fun T _ => ?_⟩
      rw [map_one, map_one]
  mul_mem' := by
    rintro a b ⟨u, hu, huf⟩ ⟨v, hv, hvf⟩
    refine ⟨u * v, ?_, ?_⟩
    · intro w
      change π w (u w * v w) = r w (a * b)
      rw [map_mul, map_mul, hu, hv]
    · intro f
      obtain ⟨S, hS⟩ := huf (ρ b f)
      obtain ⟨T, hT⟩ := hvf f
      refine ⟨S ∪ T, fun U hU => ?_⟩
      rw [map_mul, map_mul]
      change Φ U u (Φ U v f) = ρ a (ρ b f)
      rw [hT U (Finset.Subset.trans Finset.subset_union_right hU),
        hS U (Finset.Subset.trans Finset.subset_union_left hU)]
  inv_mem' := by
    rintro a ⟨u, hu, huf⟩
    refine ⟨u⁻¹, ?_, ?_⟩
    · intro v
      change π v (u v)⁻¹ = r v a⁻¹
      rw [map_inv, map_inv, hu]
    · intro f
      obtain ⟨S, hS⟩ := huf (ρ a⁻¹ f)
      refine ⟨S, fun T hT => ?_⟩
      have h := hS T hT
      rw [map_inv] at h
      change Φ T u ((ρ a).symm f) = ρ a ((ρ a).symm f) at h
      rw [LinearEquiv.apply_symm_apply] at h
      rw [map_inv, map_inv]
      change (Φ T u).symm f = (ρ a).symm f
      apply (Φ T u).injective
      rw [LinearEquiv.apply_symm_apply, h]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.CommutingProduct.CM
