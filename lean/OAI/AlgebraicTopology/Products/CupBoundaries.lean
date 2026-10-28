import OAI.AlgebraicTopology.Products.Cup
import OAI.AlgebraicTopology.Cohomology.Singular.Representatives

/-! # Cup Boundaries -/

namespace OAI.AlgebraicTopology.Products.CupBoundaries

noncomputable section

/-!
# Cup products with actual coboundaries

The primitives below come from the Leibniz identity of the actual simplicial
cup product. Degree zero is handled by the zero incoming differential of a
cochain complex indexed by the natural numbers.
-/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Cohomology.Singular.Representatives

variable {R : Type} [CommRing R]

private theorem incoming_zero (C : CochainComplex (ModuleCat.{0} R) ℕ) :
    (C.sc 0).f = 0 := by
  change C.d ((ComplexShape.up ℕ).prev 0) 0 = 0
  apply C.shape
  change ¬ (ComplexShape.up ℕ).prev 0 + 1 = 0
  omega

private theorem boundary_succ_iff (C : CochainComplex (ModuleCat.{0} R) ℕ)
    (n : ℕ) (x : C.X (n + 1)) :
    (∃ z : (C.sc (n + 1)).X₁, (C.sc (n + 1)).f z = x) ↔
      ∃ z : C.X n, C.d n (n + 1) z = x := by
  change (∃ z : C.X ((ComplexShape.up ℕ).prev (n + 1)),
    C.d ((ComplexShape.up ℕ).prev (n + 1)) (n + 1) z = x) ↔ _
  rw [CochainComplex.prev_nat_succ]

private theorem boundary_cochainCast_iff (K : SSet.{0}) (M : ModuleCat.{0} R)
    {m n : ℕ} (h : m = n) (x : (Cohomology.Singular.Basic.simplicialCochains K M).X m) :
    (∃ z : ((Cohomology.Singular.Basic.simplicialCochains K M).sc m).X₁,
      ((Cohomology.Singular.Basic.simplicialCochains K M).sc m).f z = x) ↔
    ∃ z : ((Cohomology.Singular.Basic.simplicialCochains K M).sc n).X₁,
      ((Cohomology.Singular.Basic.simplicialCochains K M).sc n).f z = Cup.cochainCast K M h x := by
  subst n
  rfl

/-- A boundary in degree zero is zero, so its left cup product has the zero
cochain as a primitive. -/
theorem cupWith_boundary_left_zero (K : SSet.{0}) {M N L : ModuleCat.{0} R}
    (B : M →ₗ[R] N →ₗ[R] L) (q : ℕ)
    (b : ((Cohomology.Singular.Basic.simplicialCochains K M).sc 0).X₁)
    (d : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.Basic.simplicialCochains K N) q) :
    ∃ z : ((Cohomology.Singular.Basic.simplicialCochains K L).sc (0 + q)).X₁,
      ((Cohomology.Singular.Basic.simplicialCochains K L).sc (0 + q)).f z =
        Cup.cupWith K B (((Cohomology.Singular.Basic.simplicialCochains K M).sc 0).f b) d.val := by
  refine ⟨0, ?_⟩
  rw [map_zero, incoming_zero (Cohomology.Singular.Basic.simplicialCochains K M)]
  exact (Cup.cupWith_zero_left K B d.val).symm

/-- A boundary in degree zero is zero, so its right cup product has the zero
cochain as a primitive. -/
theorem cupWith_boundary_right_zero (K : SSet.{0}) {M N L : ModuleCat.{0} R}
    (B : M →ₗ[R] N →ₗ[R] L) (p : ℕ)
    (c : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.Basic.simplicialCochains K M) p)
    (b : ((Cohomology.Singular.Basic.simplicialCochains K N).sc 0).X₁) :
    ∃ z : ((Cohomology.Singular.Basic.simplicialCochains K L).sc (p + 0)).X₁,
      ((Cohomology.Singular.Basic.simplicialCochains K L).sc (p + 0)).f z =
        Cup.cupWith K B c.val (((Cohomology.Singular.Basic.simplicialCochains K N).sc 0).f b) := by
  refine ⟨0, ?_⟩
  rw [map_zero, incoming_zero (Cohomology.Singular.Basic.simplicialCochains K N)]
  exact (Cup.cupWith_zero_right K B c.val).symm

/-- The cup product of an actual coboundary with a cocycle is an actual
coboundary. This includes the degree-zero incoming differential. -/
theorem cupWith_boundary_left (K : SSet.{0}) {M N L : ModuleCat.{0} R}
    (B : M →ₗ[R] N →ₗ[R] L) (p q : ℕ)
    (b : ((Cohomology.Singular.Basic.simplicialCochains K M).sc p).X₁)
    (d : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.Basic.simplicialCochains K N) q) :
    ∃ z : ((Cohomology.Singular.Basic.simplicialCochains K L).sc (p + q)).X₁,
      ((Cohomology.Singular.Basic.simplicialCochains K L).sc (p + q)).f z =
        Cup.cupWith K B (((Cohomology.Singular.Basic.simplicialCochains K M).sc p).f b) d.val := by
  cases p with
  | zero => exact cupWith_boundary_left_zero K B q b d
  | succ p =>
      obtain ⟨a, ha⟩ :=
        (boundary_succ_iff (Cohomology.Singular.Basic.simplicialCochains K M) p
          (((Cohomology.Singular.Basic.simplicialCochains K M).sc (p + 1)).f b)).mp ⟨b, rfl⟩
      rw [← ha]
      apply (boundary_cochainCast_iff K L (by omega : (p + 1) + q = p + q + 1)
        (Cup.cupWith K B ((Cohomology.Singular.Basic.simplicialCochains K M).d p (p + 1) a) d.val)).mpr
      apply (boundary_succ_iff (Cohomology.Singular.Basic.simplicialCochains K L) (p + q) _).mpr
      refine ⟨Cup.cupWith K B a d.val, ?_⟩
      have hd : (Cohomology.Singular.Basic.simplicialCochains K N).d q (q + 1) d.val = 0 :=
        (Cohomology.Singular.Representatives.mem_cochainCocycles_iff (Cohomology.Singular.Basic.simplicialCochains K N) q d.val).mp d.property
      rw [Cup.cupWith_coboundary, hd, Cup.cupWith_zero_right, smul_zero, add_zero]

/-- The cup product of a cocycle with an actual coboundary is an actual
coboundary. In positive right degree, its primitive has the sign `(-1)^p`. -/
theorem cupWith_boundary_right (K : SSet.{0}) {M N L : ModuleCat.{0} R}
    (B : M →ₗ[R] N →ₗ[R] L) (p q : ℕ)
    (c : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.Basic.simplicialCochains K M) p)
    (b : ((Cohomology.Singular.Basic.simplicialCochains K N).sc q).X₁) :
    ∃ z : ((Cohomology.Singular.Basic.simplicialCochains K L).sc (p + q)).X₁,
      ((Cohomology.Singular.Basic.simplicialCochains K L).sc (p + q)).f z =
        Cup.cupWith K B c.val (((Cohomology.Singular.Basic.simplicialCochains K N).sc q).f b) := by
  cases q with
  | zero => exact cupWith_boundary_right_zero K B p c b
  | succ q =>
      obtain ⟨a, ha⟩ :=
        (boundary_succ_iff (Cohomology.Singular.Basic.simplicialCochains K N) q
          (((Cohomology.Singular.Basic.simplicialCochains K N).sc (q + 1)).f b)).mp ⟨b, rfl⟩
      rw [← ha]
      apply (boundary_succ_iff (Cohomology.Singular.Basic.simplicialCochains K L) (p + q) _).mpr
      refine ⟨(-1 : ℤ) ^ p • Cup.cupWith K B c.val a, ?_⟩
      have hc : (Cohomology.Singular.Basic.simplicialCochains K M).d p (p + 1) c.val = 0 :=
        (Cohomology.Singular.Representatives.mem_cochainCocycles_iff (Cohomology.Singular.Basic.simplicialCochains K M) p c.val).mp c.property
      rw [map_zsmul, Cup.cupWith_coboundary, hc, Cup.cupWith_zero_left, map_zero, zero_add,
        smul_smul, ← mul_pow]
      simp

end

end OAI.AlgebraicTopology.Products.CupBoundaries
