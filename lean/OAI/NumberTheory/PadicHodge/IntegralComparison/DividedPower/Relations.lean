import Mathlib

/-! # Relations -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.Relations

noncomputable section

/-!
# IntegralComparison: imposing relations in a divided-power ideal

Relations inside the divided-power ideal generate a divided-power-stable
ideal. The quotient has its actual induced divided powers and a universal
mapping property for divided-power maps annihilating those relations.
-/

universe u v

variable {A : Type u} [CommRing A] {I : Ideal A} (δ : DividedPowers I)
variable (S : Set A) (hS : S ⊆ I)

def relationIdeal : Ideal A :=
  Ideal.span {y | ∃ (n : ℕ) (_ : n ≠ 0) (x : A) (_ : x ∈ S), y = δ.dpow n x}

include hS in
lemma relationIdeal_stable : DividedPowers.IsSubDPIdeal δ (relationIdeal δ S) where
  isSubideal := δ.dpow_span_isSubideal hS
  dpow_mem _n hn _ hx := DividedPowers.SubDPIdeal.dpow_mem_span_of_mem_span δ hS hn hx

include hS in
lemma relation_mem {x : A} (hx : x ∈ S) : x ∈ relationIdeal δ S :=
  Ideal.subset_span ⟨1, one_ne_zero, x, hx, (δ.dpow_one (hS hx)).symm⟩

include hS in
lemma stable_intersection : DividedPowers.IsSubDPIdeal δ (relationIdeal δ S ⊓ I) := by
  rw [inf_eq_left.mpr (relationIdeal_stable δ S hS).isSubideal]
  exact relationIdeal_stable δ S hS

abbrev dividedPowers : DividedPowers (I.map (Ideal.Quotient.mk (relationIdeal δ S))) :=
  DividedPowers.Quotient.dividedPowers δ (stable_intersection δ S hS)

def quotientMap : DividedPowers.DPMorphism δ (Relations.dividedPowers δ S hS) where
  toRingHom := Ideal.Quotient.mk (relationIdeal δ S)
  ideal_comp := le_rfl
  dpow_comp _ hx := DividedPowers.Quotient.dpow_apply δ (stable_intersection δ S hS) hx

/-- Imposing relations inside the divided-power ideal preserves the closed subscheme. -/
def residueEquiv :
    (A ⧸ relationIdeal δ S) ⧸ I.map (Ideal.Quotient.mk (relationIdeal δ S)) ≃+* A ⧸ I :=
  DoubleQuot.quotQuotEquivQuotOfLE (relationIdeal_stable δ S hS).isSubideal

lemma residueEquiv_mk (x : A) :
    residueEquiv δ S hS (Ideal.Quotient.mk _ (Ideal.Quotient.mk (relationIdeal δ S) x)) =
      Ideal.Quotient.mk I x := rfl

variable {T : Type v} [CommRing T] {K : Ideal T} {ε : DividedPowers K}
variable (φ : DividedPowers.DPMorphism δ ε) (hφ : ∀ x ∈ S, φ x = 0)

include hS hφ in
lemma relationIdeal_killed : relationIdeal δ S ≤ RingHom.ker φ.toRingHom := by
  apply Ideal.span_le.mpr
  rintro y ⟨n, hn, x, hx, rfl⟩
  change φ.toRingHom (δ.dpow n x) = 0
  rw [← φ.dpow_comp x (hS hx)]
  change ε.dpow n (φ x) = 0
  rw [hφ x hx, ε.dpow_eval_zero hn]

def liftRingMap : A ⧸ relationIdeal δ S →+* T :=
  Ideal.Quotient.lift (relationIdeal δ S) φ.toRingHom (relationIdeal_killed δ S hS φ hφ)

def lift : DividedPowers.DPMorphism (Relations.dividedPowers δ S hS) ε where
  toRingHom := liftRingMap δ S hS φ hφ
  ideal_comp := by
    rw [Ideal.map_map]
    exact φ.ideal_comp
  dpow_comp {n} y hy := by
    obtain ⟨x, hx, rfl⟩ :=
      (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk (relationIdeal δ S)) Ideal.Quotient.mk_surjective).mp hy
    change ε.dpow n (φ x) =
      liftRingMap δ S hS φ hφ ((Relations.dividedPowers δ S hS).dpow n (Ideal.Quotient.mk (relationIdeal δ S) x))
    rw [DividedPowers.Quotient.dpow_apply δ (stable_intersection δ S hS) hx]
    exact φ.dpow_comp x hx

lemma lift_comp : (Relations.lift δ S hS φ hφ).comp (quotientMap δ S hS) = φ := by
  apply DFunLike.ext
  intro x
  rfl

lemma lift_unique (ψ : DividedPowers.DPMorphism (Relations.dividedPowers δ S hS) ε)
    (hψ : ψ.comp (quotientMap δ S hS) = φ) : ψ = Relations.lift δ S hS φ hφ := by
  apply DFunLike.ext
  intro y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact DFunLike.congr_fun hψ x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.Relations
