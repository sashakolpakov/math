import OAI.RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits

/-! # Central Product -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.CentralProduct.Construction

noncomputable section

section

/-! The adelic circle extension as the restricted product of local covers,
with central scalars at different places identified. The quotient, its
projection, and the local inclusions are constructed, not supplied. -/

open Filter
open scoped Classical

variable {I : Type*} {M G : I → Type*}
  [∀ v, Group (M v)] [∀ v, Group (G v)]
  (K : ∀ v, Subgroup (M v)) (L : ∀ v, Subgroup (G v))
  (c : ∀ v, Circle →* M v)

def scalarRelations : Set (RestrictedLimits.Construction.RestrictedGroup K) :=
  {x | ∃ v w z, x = RestrictedLimits.Construction.includePlace K v (c v z) * (RestrictedLimits.Construction.includePlace K w (c w z))⁻¹}

def scalarKernel : Subgroup (RestrictedLimits.Construction.RestrictedGroup K) :=
  Subgroup.normalClosure (scalarRelations K c)

instance scalarKernel_normal : (scalarKernel K c).Normal :=
  Subgroup.normalClosure_normal

abbrev AdelicCover := RestrictedLimits.Construction.RestrictedGroup K ⧸ scalarKernel K c

def assembleCover : RestrictedLimits.Construction.RestrictedGroup K →* AdelicCover K c :=
  QuotientGroup.mk' (scalarKernel K c)

def includeCover (v : I) : M v →* AdelicCover K c :=
  (assembleCover K c).comp (RestrictedLimits.Construction.includePlace K v)

theorem includeCover_scalar_eq (v w : I) (z : Circle) :
    includeCover K c v (c v z) = includeCover K c w (c w z) := by
  apply eq_of_mul_inv_eq_one
  change assembleCover K c (RestrictedLimits.Construction.includePlace K v (c v z)) *
    (assembleCover K c (RestrictedLimits.Construction.includePlace K w (c w z)))⁻¹ = 1
  rw [← map_inv, ← map_mul]
  apply (QuotientGroup.eq_one_iff _).mpr
  exact Subgroup.subset_normalClosure ⟨v, w, z, rfl⟩

variable (p : ∀ v, M v →* G v)
  (hp : ∀ᶠ v in cofinite, Set.MapsTo (p v) (K v) (L v))
  (hc : ∀ v z, p v (c v z) = 1)

include hc in
theorem scalarKernel_le_projectionKernel :
    scalarKernel K c ≤ (RestrictedLimits.Construction.restrictedMap K L p hp).ker := by
  apply Subgroup.normalClosure_le_normal
  rintro x ⟨v, w, z, rfl⟩
  apply MonoidHom.mem_ker.mpr
  simp [RestrictedLimits.Construction.restrictedMap_includePlace, hc]

def adelicProjection : AdelicCover K c →* RestrictedLimits.Construction.RestrictedGroup L :=
  QuotientGroup.lift (scalarKernel K c) (RestrictedLimits.Construction.restrictedMap K L p hp)
    (scalarKernel_le_projectionKernel K L c p hp hc)

@[simp] theorem adelicProjection_assemble (x : RestrictedLimits.Construction.RestrictedGroup K) :
    adelicProjection K L c p hp hc (assembleCover K c x) =
      RestrictedLimits.Construction.restrictedMap K L p hp x := rfl

@[simp] theorem adelicProjection_include (v : I) (x : M v) :
    adelicProjection K L c p hp hc (includeCover K c v x) =
      RestrictedLimits.Construction.includePlace L v (p v x) := RestrictedLimits.Construction.restrictedMap_includePlace K L p hp v x

variable [∀ v, TopologicalSpace (M v)] [∀ v, TopologicalSpace (G v)]

theorem assembleCover_continuous : Continuous (assembleCover K c) :=
  QuotientGroup.continuous_mk

def assembleCoverContinuous : RestrictedLimits.Construction.RestrictedGroup K →ₜ* AdelicCover K c :=
  ⟨assembleCover K c, assembleCover_continuous K c⟩

def includeCoverContinuous (v : I) : M v →ₜ* AdelicCover K c :=
  (assembleCoverContinuous K c).comp (RestrictedLimits.Construction.includePlaceContinuous K v)

end

/-! Finite products of local scalars in the adelic quotient. -/

open scoped Classical

variable {I : Type*} {G : I → Type*} [∀ v, Group (G v)]
  (K : ∀ v, Subgroup (G v)) (c : ∀ v, Circle →* G v)

/-- A finite family of local scalar operators, before taking the quotient. -/
def finiteScalarFamily (xs : List (I × Circle)) : RestrictedLimits.Construction.RestrictedGroup K :=
  (xs.map (fun p => RestrictedLimits.Construction.includePlace K p.1 (c p.1 p.2))).prod

theorem assemble_finiteScalarFamily (w : I) (xs : List (I × Circle)) :
    assembleCover K c (finiteScalarFamily K c xs) =
      includeCover K c w (c w ((xs.map Prod.snd).prod)) := by
  induction xs with
  | nil => simp [finiteScalarFamily]
  | cons p xs ih =>
      change assembleCover K c
        (RestrictedLimits.Construction.includePlace K p.1 (c p.1 p.2) * finiteScalarFamily K c xs) = _
      rw [map_mul, ih]
      change includeCover K c p.1 (c p.1 p.2) *
        includeCover K c w (c w ((xs.map Prod.snd).prod)) = _
      rw [includeCover_scalar_eq K c p.1 w p.2]
      simp only [List.map_cons, List.prod_cons, map_mul]

theorem finiteScalarFamily_mem_kernel (w : I) (xs : List (I × Circle))
    (h : (xs.map Prod.snd).prod = 1) :
    finiteScalarFamily K c xs ∈ scalarKernel K c := by
  apply (QuotientGroup.eq_one_iff _).mp
  change assembleCover K c (finiteScalarFamily K c xs) = 1
  rw [assemble_finiteScalarFamily K c w, h, map_one, map_one]

theorem assemble_eq_of_finiteScalarFamily (w : I)
    (a b : RestrictedLimits.Construction.RestrictedGroup K) (xs : List (I × Circle))
    (hab : a * b⁻¹ = finiteScalarFamily K c xs)
    (hprod : (xs.map Prod.snd).prod = 1) :
    assembleCover K c a = assembleCover K c b := by
  apply mul_inv_eq_one.mp
  rw [← map_inv, ← map_mul, hab, assemble_finiteScalarFamily K c w, hprod]
  simp

theorem finiteScalarFamily_finset_apply (s : Finset I) (z : I → Circle) (w : I) :
    finiteScalarFamily K c (s.toList.map (fun v => (v, z v))) w =
      c w (if w ∈ s then z w else 1) := by
  change RestrictedProduct.evalMonoidHom G w
    (finiteScalarFamily K c (s.toList.map (fun v => (v, z v)))) = _
  rw [finiteScalarFamily, map_list_prod]
  simp only [List.map_map, Function.comp_def]
  have he : (fun v => RestrictedProduct.evalMonoidHom G w
      (RestrictedLimits.Construction.includePlace K v (c v (z v)))) =
      fun v => c w (if w = v then z v else 1) := by
    funext v
    change RestrictedLimits.Construction.includePlace K v (c v (z v)) w = _
    by_cases h : w = v
    · subst v; simp
    · simp [h]
  rw [he]
  have hp := map_list_prod (c w) (s.toList.map (fun v => if w = v then z v else 1))
  simp only [List.map_map, Function.comp_def] at hp
  rw [← hp, Finset.prod_map_toList]
  congr 1
  exact Finset.prod_ite_eq s w z

theorem scalar_family_eq_finite (s : Finset I) (z : I → Circle)
    (hz : ∀ v ∉ s, z v = 1) (a : RestrictedLimits.Construction.RestrictedGroup K)
    (ha : ∀ v, a v = c v (z v)) :
    a = finiteScalarFamily K c (s.toList.map (fun v => (v, z v))) := by
  apply RestrictedProduct.ext
  intro v
  rw [ha v, finiteScalarFamily_finset_apply]
  by_cases h : v ∈ s
  · rw [ite_eq_left h]
  · rw [ite_eq_right h, hz v h]

theorem assemble_scalar_family_eq_one (w : I) (s : Finset I) (z : I → Circle)
    (hz : ∀ v ∉ s, z v = 1) (hp : HasProd z 1) (a : RestrictedLimits.Construction.RestrictedGroup K)
    (ha : ∀ v, a v = c v (z v)) : assembleCover K c a = 1 := by
  have hprod : ∏ v ∈ s, z v = 1 := (hasProd_prod_of_ne_finset_one hz).unique hp
  rw [scalar_family_eq_finite K c s z hz a ha, assemble_finiteScalarFamily K c w]
  simp only [List.map_map, Function.comp_def, Finset.prod_map_toList, hprod, map_one]

theorem assemble_eq_of_scalar_product (w : I) (s : Finset I) (z : I → Circle)
    (hz : ∀ v ∉ s, z v = 1) (hp : HasProd z 1) (a b : RestrictedLimits.Construction.RestrictedGroup K)
    (hab : ∀ v, a v * (b v)⁻¹ = c v (z v)) : assembleCover K c a = assembleCover K c b := by
  apply mul_inv_eq_one.mp
  rw [← map_inv, ← map_mul]
  exact assemble_scalar_family_eq_one K c w s z hz hp (a * b⁻¹) hab

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.CentralProduct.Construction
