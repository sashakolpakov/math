import OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.Transfer
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PrincipalBase

/-! # Divided Power Descent -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.DividedPowerDescent

noncomputable section

/-! Compatible divided powers on a principal base ideal descend along
any family of algebra maps which jointly detects equality. -/

universe u v w z

variable (R : Type u) [CommRing R] (r : R)
  (δR : DividedPowers (Ideal.span {r}))
  (A : Type v) [CommRing A] [Algebra R A]
  {ι : Type w} (B : ι → Type z) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
  (δ : ∀ i, DividedPowers (Ideal.span {algebraMap R (B i) r}))
  (f : ∀ i, A →ₐ[R] B i)
  (hbase : ∀ i, DividedPowers.IsDPMorphism δR (δ i) (algebraMap R (B i)))
  (hinj : ∀ x y : A, (∀ i, f i x = f i y) → x = y)

private theorem ideal_map (i : ι) :
    Ideal.span {algebraMap R A r} ≤
      (Ideal.span {algebraMap R (B i) r}).comap (f i).toRingHom := by
  rw [Ideal.span_le]
  rintro x (rfl : x = _)
  change f i (algebraMap R A r) ∈ Ideal.span {algebraMap R (B i) r}
  rw [(f i).commutes]
  exact Ideal.subset_span (Set.mem_singleton _)

include hbase in
private theorem exists_value (n : ℕ) {x : A} (hx : x ∈ Ideal.span {algebraMap R A r}) :
    ∃ y : A, (n ≠ 0 → y ∈ Ideal.span {algebraMap R A r}) ∧
      ∀ i, f i y = (δ i).dpow n (f i x) := by
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.mp hx
  refine ⟨a ^ n * algebraMap R A (δR.dpow n r), ?_, ?_⟩
  · intro hn
    have hm := Ideal.mem_map_of_mem (algebraMap R A)
      (δR.dpow_mem hn (Ideal.subset_span (Set.mem_singleton r)))
    rw [Ideal.map_span, Set.image_singleton] at hm
    exact Ideal.mul_mem_left _ _ hm
  · intro i
    rw [map_mul, map_pow, (f i).commutes, map_mul, (f i).commutes,
      mul_comm (algebraMap R (B i) r),
      (δ i).dpow_mul (Ideal.subset_span (Set.mem_singleton _)),
      (hbase i).dpow_comp r (Ideal.subset_span (Set.mem_singleton r))]

def dividedPowers : DividedPowers (Ideal.span {algebraMap R A r}) :=
  DividedPower.Transfer.dividedPowers (Ideal.span {algebraMap R A r})
    (fun i => Ideal.span {algebraMap R (B i) r}) δ (fun i => (f i).toRingHom)
    hinj (ideal_map R r A B f) (exists_value R r δR A B δ f hbase)

theorem map_isDPMorphism (i : ι) :
    DividedPowers.IsDPMorphism (dividedPowers R r δR A B δ f hbase hinj) (δ i)
      (f i).toRingHom := by
  refine ⟨Ideal.map_le_iff_le_comap.mpr (ideal_map R r A B f i), ?_⟩
  intro n x hx
  exact (DividedPower.Transfer.dividedPowers_map (Ideal.span {algebraMap R A r})
    (fun i => Ideal.span {algebraMap R (B i) r}) δ (fun i => (f i).toRingHom)
    hinj (ideal_map R r A B f) (exists_value R r δR A B δ f hbase) n hx i).symm

attribute [local irreducible] dividedPowers

theorem base_isDPMorphism :
    DividedPowers.IsDPMorphism δR (dividedPowers R r δR A B δ f hbase hinj)
      (algebraMap R A) := by
  refine ⟨by rw [Ideal.map_span, Set.image_singleton], ?_⟩
  intro n x hx
  apply hinj
  intro i
  have hxA : algebraMap R A x ∈ Ideal.span {algebraMap R A r} := by
    have h := Ideal.mem_map_of_mem (algebraMap R A) hx
    rwa [Ideal.map_span, Set.image_singleton] at h
  calc
    f i ((dividedPowers R r δR A B δ f hbase hinj).dpow n (algebraMap R A x)) =
        (δ i).dpow n (f i (algebraMap R A x)) :=
      (map_isDPMorphism R r δR A B δ f hbase hinj i).map_dpow hxA
    _ = (δ i).dpow n (algebraMap R (B i) x) := congrArg ((δ i).dpow n) ((f i).commutes x)
    _ = algebraMap R (B i) (δR.dpow n x) := (hbase i).dpow_comp x hx
    _ = f i (algebraMap R A (δR.dpow n x)) := ((f i).commutes _).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.DividedPowerDescent
