import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Hecke
import Mathlib.GroupTheory.Coset.Basic

/-! # Cosets -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Product.Cosets.Construction

noncomputable section

/-!
Raw double-coset support respects products. A commutative multiplier
factor contributes exactly one coset; it is not replicated per block.
-/

section Pi

variable {I : Type*} {G : I → Type*} [∀ i, Group (G i)] (U : ∀ i, Subgroup (G i))

def piCosetMap : ((∀ i, G i) ⧸ Subgroup.pi Set.univ U) → ∀ i, G i ⧸ U i :=
  Quotient.lift (fun g i => QuotientGroup.mk (g i)) (by
    intro g k h
    funext i
    apply Quotient.sound
    apply QuotientGroup.leftRel_apply.mpr
    exact ((Subgroup.mem_pi Set.univ).mp (QuotientGroup.leftRel_apply.mp h)) i (Set.mem_univ i))

theorem piCosetMap_bijective : Function.Bijective (piCosetMap U) := by
  constructor
  · intro x y
    induction x using Quotient.inductionOn with
    | h g =>
      induction y using Quotient.inductionOn with
      | h k =>
        intro he
        apply Quotient.sound
        apply QuotientGroup.leftRel_apply.mpr
        apply (Subgroup.mem_pi Set.univ).mpr
        intro i _
        exact QuotientGroup.leftRel_apply.mp (Quotient.exact (congrFun he i))
  · intro x
    have hx (i : I) : ∃ g : G i, QuotientGroup.mk g = x i := Quotient.exists_rep (x i)
    choose g hg using hx
    exact ⟨QuotientGroup.mk g, funext hg⟩

def piCosetEquiv : ((∀ i, G i) ⧸ Subgroup.pi Set.univ U) ≃ ∀ i, G i ⧸ U i :=
  Equiv.ofBijective (piCosetMap U) (piCosetMap_bijective U)

theorem pi_raw_support_iff (g : ∀ i, G i) (x : (∀ i, G i) ⧸ Subgroup.pi Set.univ U) :
    x ∈ Hecke.Construction.rawRightCosetSupport (Subgroup.pi Set.univ U) g ↔
      ∀ i, piCosetEquiv U x i ∈ Hecke.Construction.rawRightCosetSupport (U i) (g i) := by
  induction x using Quotient.inductionOn with
  | h x =>
    change QuotientGroup.mk x ∈ Hecke.Construction.rawRightCosetSupport _ g ↔
      ∀ i, QuotientGroup.mk (x i) ∈ Hecke.Construction.rawRightCosetSupport (U i) (g i)
    simp_rw [Hecke.Construction.rawRightCosetSupport_mk_iff]
    constructor
    · rintro ⟨k, l, rfl⟩ i
      exact ⟨⟨k.val i, ((Subgroup.mem_pi Set.univ).mp k.property) i (Set.mem_univ i)⟩,
        ⟨l.val i, ((Subgroup.mem_pi Set.univ).mp l.property) i (Set.mem_univ i)⟩, rfl⟩
    · intro hx
      choose k l hkl using hx
      exact ⟨⟨fun i => (k i).val, (Subgroup.mem_pi Set.univ).mpr (fun i _ => (k i).property)⟩,
        ⟨fun i => (l i).val, (Subgroup.mem_pi Set.univ).mpr (fun i _ => (l i).property)⟩, funext hkl⟩

def piRawSupportEquiv (g : ∀ i, G i) :
    Hecke.Construction.rawRightCosetSupport (Subgroup.pi Set.univ U) g ≃
      ∀ i, Hecke.Construction.rawRightCosetSupport (U i) (g i) :=
  ((piCosetEquiv U).subtypeEquiv (pi_raw_support_iff U g)).trans Equiv.subtypePiEquivPi

end Pi

section Prod

variable {G H : Type*} [Group G] [Group H] (U : Subgroup G) (V : Subgroup H)

theorem prod_raw_support_iff (g : G) (h : H) (x : (G × H) ⧸ U.prod V) :
    x ∈ Hecke.Construction.rawRightCosetSupport (U.prod V) (g, h) ↔
      (QuotientGroup.prodEquiv U V x).1 ∈ Hecke.Construction.rawRightCosetSupport U g ∧
      (QuotientGroup.prodEquiv U V x).2 ∈ Hecke.Construction.rawRightCosetSupport V h := by
  induction x using Quotient.inductionOn with
  | h x =>
    change QuotientGroup.mk x ∈ Hecke.Construction.rawRightCosetSupport _ (g, h) ↔
      QuotientGroup.mk x.1 ∈ Hecke.Construction.rawRightCosetSupport U g ∧
      QuotientGroup.mk x.2 ∈ Hecke.Construction.rawRightCosetSupport V h
    rw [Hecke.Construction.rawRightCosetSupport_mk_iff, Hecke.Construction.rawRightCosetSupport_mk_iff, Hecke.Construction.rawRightCosetSupport_mk_iff]
    constructor
    · rintro ⟨k, l, rfl⟩
      exact ⟨⟨⟨k.val.1, k.property.1⟩, ⟨l.val.1, l.property.1⟩, rfl⟩,
        ⟨⟨k.val.2, k.property.2⟩, ⟨l.val.2, l.property.2⟩, rfl⟩⟩
    · rintro ⟨⟨k₁, l₁, h₁⟩, ⟨k₂, l₂, h₂⟩⟩
      exact ⟨⟨(k₁.val, k₂.val), ⟨k₁.property, k₂.property⟩⟩,
        ⟨(l₁.val, l₂.val), ⟨l₁.property, l₂.property⟩⟩, Prod.ext h₁ h₂⟩

def prodRawSupportEquiv (g : G) (h : H) :
    Hecke.Construction.rawRightCosetSupport (U.prod V) (g, h) ≃
      Hecke.Construction.rawRightCosetSupport U g × Hecke.Construction.rawRightCosetSupport V h :=
  ((QuotientGroup.prodEquiv U V).subtypeEquiv (prod_raw_support_iff U V g h)).trans
    Equiv.subtypeProdEquivProd

end Prod

variable {G : Type*} [CommGroup G] (U : Subgroup G) (g : G)

theorem comm_raw_support_eq (x : Hecke.Construction.rawRightCosetSupport U g) :
    x.val = QuotientGroup.mk g⁻¹ := by
  obtain ⟨k, hk⟩ := MulAction.mem_orbit_iff.mp x.property
  change QuotientGroup.mk (k.val * g⁻¹) = x.val at hk
  rw [← hk]
  apply Quotient.sound
  apply QuotientGroup.leftRel_apply.mpr
  simp [mul_comm, mul_left_comm]

instance commRawSupportUnique : Unique (Hecke.Construction.rawRightCosetSupport U g) where
  default := ⟨QuotientGroup.mk g⁻¹, MulAction.mem_orbit_self _⟩
  uniq x := Subtype.ext (comm_raw_support_eq U g x)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Product.Cosets.Construction
