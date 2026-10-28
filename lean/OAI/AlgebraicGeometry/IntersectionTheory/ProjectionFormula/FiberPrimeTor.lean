import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.AnnihilatedFiberTor

/-! # Fiber Prime Tor -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.FiberPrimeTor

noncomputable section

/-! A prime quotient lying on the parameter fiber is identified with
the actual mapped quotient on that fiber. Its native Tor pairing with
a parameter-regular module is therefore the fiber Tor pairing. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory

universe u

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (hs : Function.Surjective (algebraMap R S))

def quotientEquiv (q : Ideal R) (hq : RingHom.ker (algebraMap R S) ≤ q) :
    (R ⧸ q) ≃ₗ[R] (ModuleCat.restrictScalars (algebraMap R S)).obj (.of S (S ⧸ q.map (algebraMap R S))) := by
  let T := S ⧸ q.map (algebraMap R S)
  let f := Algebra.ofId R T
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective.comp hs
  have hk : RingHom.ker f.toRingHom = q := by
    change RingHom.ker ((Ideal.Quotient.mk (q.map (algebraMap R S))).comp (algebraMap R S)) = q
    rw [← RingHom.comap_ker, Ideal.mk_ker, Ideal.comap_map_of_surjective _ hs,
      ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hq]
  let eT : T ≃ₗ[R] (ModuleCat.restrictScalars (algebraMap R S)).obj (.of S T) :=
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r t => (IsScalarTower.algebraMap_smul S r t).symm }
  exact ((Submodule.quotEquivOfEq _ _ hk.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective hf).toLinearEquiv).trans eT

theorem annihilated (q : Ideal R) (r : R) (hrq : r ∈ q) :
    ∀ m : R ⧸ q, r • m = 0 := by
  intro m
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective m
  change Ideal.Quotient.mk q (r * a) = 0
  exact (Ideal.Quotient.eq_zero_iff_mem (I := q)).mpr (q.mul_mem_right a hrq)

include hs in
theorem euler (r : R) (hr : IsSMulRegular R r)
    (hk : RingHom.ker (algebraMap R S) = Ideal.span {r}) (q : Ideal R) (hrq : r ∈ q)
    (N : ModuleCat.{u} R) (hN : IsSMulRegular N r) (N₀ : ModuleCat.{u} S)
    (eN : QuotSMulTop r N ≃ₗ[R] (ModuleCat.restrictScalars (algebraMap R S)).obj N₀) (d : ℕ) :
    Tor.Euler.euler R (.of R (R ⧸ q)) N d =
      Tor.Euler.euler S (.of S (S ⧸ q.map (algebraMap R S))) N₀ d := by
  have hq : RingHom.ker (algebraMap R S) ≤ q := by
    rw [hk]
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hrq)
  let M := ModuleCat.of R (R ⧸ q)
  have hM : ∀ m : M, r • m = 0 := annihilated R q r hrq
  let eM : QuotSMulTop r M ≃ₗ[R] M :=
    Submodule.quotEquivOfEqBot _ (AnnihilatedParameterComplex.submodule_eq_bot R r M hM)
  exact AnnihilatedFiberTor.euler R S r hr (algebraMap R S) hs hk M N hM hN
    (.of S (S ⧸ q.map (algebraMap R S))) N₀ (eM.trans (quotientEquiv R S hs q hq)) eN d

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.FiberPrimeTor
