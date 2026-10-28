import OAI.AlgebraicTopology.Products.Cap
import OAI.AlgebraicTopology.Products.Cup

/-! # Cap Boundary -/

namespace OAI.AlgebraicTopology.Products.CapBoundary

noncomputable section

section

/-!
# The signed boundary identity for the actual cap product

The universal chain-valued cochain turns the bilinear cup-product Leibniz
identity into the cap-product boundary identity. Thus no independent chain
law is assumed.
-/

open _root_.CategoryTheory
open scoped Simplicial

variable {R : Type} [CommRing R]

/-- Degree transport of cochains is adjoint to inverse degree transport of
the chains on which they are evaluated. -/
theorem degreewiseChainDualEquiv_cochainCast_apply (K : SSet.{0})
    (M : ModuleCat.{0} R) {m n : ℕ} (h : m = n)
    (c : (Cohomology.Singular.Basic.simplicialCochains K M).X m)
    (z : (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).X n) :
    Cohomology.Singular.ChainDual.degreewiseChainDualEquiv K M n (Cup.cochainCast K M h c) z =
      Cohomology.Singular.ChainDual.degreewiseChainDualEquiv K M m c (Cap.chainCast K h.symm z) := by
  subst n
  rfl

/-- The cap product is adjoint to the cup product with scalar multiplication
as its coefficient pairing. -/
theorem cap_cupWith_pairing (K : SSet.{0}) (M : ModuleCat.{0} R) {p q : ℕ}
    (c : (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)).X p)
    (b : (Cohomology.Singular.Basic.simplicialCochains K M).X q)
    (z : (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).X (p + q)) :
    Cohomology.Singular.ChainDual.degreewiseChainDualEquiv K M (p + q) (Cup.cupWith K (LinearMap.lsmul R M) c b) z =
      Cohomology.Singular.ChainDual.degreewiseChainDualEquiv K M q b (Cap.cap K p q c z) := by
  have h : Cohomology.Singular.ChainDual.degreewiseChainDualEquiv K M (p + q) (Cup.cupWith K (LinearMap.lsmul R M) c b) =
      (Cohomology.Singular.ChainDual.degreewiseChainDualEquiv K M q b).comp (Cap.cap K p q c) := by
    apply Cohomology.Singular.ChainDual.chainFunctional_ext K M
    intro s
    simp only [Cohomology.Singular.ChainDual.degreewiseChainDualEquiv_simplex, Cup.evaluation_cupWith, LinearMap.lsmul_apply,
      LinearMap.comp_apply, Cap.cap_simplex, map_smul]
  exact LinearMap.congr_fun h z

/-- The signed cap-product boundary identity with the cochain evaluated on
the front face. -/
theorem cap_boundary (K : SSet.{0}) (p q : ℕ)
    (c : (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)).X p)
    (z : (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).X (p + q + 1)) :
    Cap.cap K p q c ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).d (p + q + 1) (p + q) z) =
      Cap.cap K (p + 1) q ((Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)).d p (p + 1) c)
        (Cap.chainCast K (by omega : p + q + 1 = (p + 1) + q) z) +
      ((-1 : ℤ) ^ p) •
        ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).d (q + 1) q (Cap.cap K p (q + 1) c z)) := by
  have h := congrArg
    (fun u : (Cohomology.Singular.Basic.simplicialCochains K ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).X q)).X
        (p + q + 1) =>
      Cohomology.Singular.ChainDual.degreewiseChainDualEquiv K ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).X q)
        (p + q + 1) u z)
    (Cup.cupWith_coboundary K (LinearMap.lsmul R ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).X q))
      c (Cap.simplexCochain K q))
  rw [Cohomology.Singular.ChainDual.chainCochainPairing_coboundary] at h
  simp only [map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply,
    degreewiseChainDualEquiv_cochainCast_apply, cap_cupWith_pairing,
    Cap.simplexCochain_dual, LinearMap.id_apply] at h
  erw [cap_cupWith_pairing K ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).X q)
    (p := p) (q := q + 1) c
    ((Cohomology.Singular.Basic.simplicialCochains K ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).X q)).d q (q + 1)
      (Cap.simplexCochain K q)) z] at h
  simpa only [Cap.simplexCochain_coboundary_dual] using h

/-- The same boundary identity solved for the boundary of the cap product. -/
theorem boundary_cap (K : SSet.{0}) (p q : ℕ)
    (c : (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)).X p)
    (z : (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).X (p + q + 1)) :
    (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).d (q + 1) q (Cap.cap K p (q + 1) c z) =
      ((-1 : ℤ) ^ p) •
        (Cap.cap K p q c ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).d (p + q + 1) (p + q) z) -
          Cap.cap K (p + 1) q ((Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)).d p (p + 1) c)
            (Cap.chainCast K (by omega : p + q + 1 = (p + 1) + q) z)) := by
  rw [cap_boundary K p q c z, add_sub_cancel_left, smul_smul]
  have hs : ((-1 : ℤ) ^ p) * ((-1 : ℤ) ^ p) = 1 := by
    rw [← mul_pow]
    simp
  rw [hs, one_smul]

/-- The cap-product boundary identity for genuine continuous singular
cochains and chains. -/
theorem singularCap_boundary (X : TopCat.{0}) (p q : ℕ)
    (c : (Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).X p)
    (z : (Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).X (p + q + 1)) :
    Cap.singularCap X p q c ((Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).d (p + q + 1) (p + q) z) =
      Cap.singularCap X (p + 1) q ((Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).d p (p + 1) c)
        (Cap.chainCast (TopCat.toSSet.obj X)
          (by omega : p + q + 1 = (p + 1) + q) z) +
      ((-1 : ℤ) ^ p) •
        ((Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).d (q + 1) q (Cap.singularCap X p (q + 1) c z)) :=
  cap_boundary (TopCat.toSSet.obj X) p q c z

end

/-!
# The cap product on actual cohomology and homology

The signed boundary identity proves that cocycles cap cycles to cycles, that
boundaries in either input give boundaries, and hence that the cap product
descends to the existing categorical (co)homology groups. Degree zero is
included throughout.
-/

open _root_.CategoryTheory

variable {R : Type} [CommRing R]

@[simp]
theorem chainCast_symm_apply (K : SSet.{0}) {m n : ℕ} (h : m = n)
    (z : (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).X m) :
    Cap.chainCast K h.symm (Cap.chainCast K h z) = z := by
  subst n
  rfl

/-- The actual differential is compatible with transport of its source degree. -/
@[simp]
theorem boundary_chainCast (K : SSet.{0}) {m n : ℕ} (h : m = n) (j : ℕ)
    (z : (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).X m) :
    (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).d n j (Cap.chainCast K h z) =
      (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).d m j z := by
  subst n
  rfl

/-- A cocycle caps a cycle to a cycle, including when the output degree is zero. -/
theorem cap_mem_chainCycles (K : SSet.{0}) (p q : ℕ)
    (c : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)) p)
    (z : Cohomology.Singular.ChainRepresentatives.chainCycles (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K) (p + q)) :
    Cap.cap K p q c.val z.val ∈ Cohomology.Singular.ChainRepresentatives.chainCycles (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K) q := by
  cases q with
  | zero => exact Cohomology.Singular.ChainRepresentatives.mem_chainCycles_zero _ _
  | succ q =>
    apply (Cohomology.Singular.ChainRepresentatives.mem_chainCycles_iff_succ (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K) q _).mpr
    rw [boundary_cap K p q c.val z.val]
    have hz := Cohomology.Singular.ChainRepresentatives.chainCycle_d_eq_zero (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K)
      (p + q + 1) (p + q) z
    have hc := Cohomology.Singular.Evaluation.cochainCocycle_d_eq_zero (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R))
      p (p + 1) c
    simp only [hz, hc, map_zero, LinearMap.zero_apply, sub_self, smul_zero]

/-- The cap product restricted to genuine cocycles and cycles. -/
def capCycles (K : SSet.{0}) (p q : ℕ) :
    Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)) p →ₗ[R]
      Cohomology.Singular.ChainRepresentatives.chainCycles (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K) (p + q) →ₗ[R]
        Cohomology.Singular.ChainRepresentatives.chainCycles (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K) q where
  toFun c :=
    (((Cap.cap K p q c.val).comp
      (Cohomology.Singular.ChainRepresentatives.chainCycles (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K) (p + q)).subtype).codRestrict
        (Cohomology.Singular.ChainRepresentatives.chainCycles (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K) q)
        (fun z => cap_mem_chainCycles K p q c z))
  map_add' c d := by
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    change Cap.cap K p q (c.val + d.val) z.val =
      Cap.cap K p q c.val z.val + Cap.cap K p q d.val z.val
    simp only [map_add, LinearMap.add_apply]
  map_smul' r c := by
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    change Cap.cap K p q (r • c.val) z.val = r • Cap.cap K p q c.val z.val
    simp only [map_smul, LinearMap.smul_apply]

@[simp]
theorem capCycles_val (K : SSet.{0}) (p q : ℕ)
    (c : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)) p)
    (z : Cohomology.Singular.ChainRepresentatives.chainCycles (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K) (p + q)) :
    (capCycles K p q c z).val = Cap.cap K p q c.val z.val := rfl

/-- Capping a boundary with a cocycle gives an explicitly witnessed boundary. -/
theorem cap_cocycle_boundary_exists (K : SSet.{0}) (p q : ℕ)
    (c : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)) p)
    (i : ℕ) (w : (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).X i) :
    ∃ v : (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).X (q + 1),
      (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).d (q + 1) q v =
        Cap.cap K p q c.val ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).d i (p + q) w) := by
  by_cases hi : (ComplexShape.down ℕ).Rel i (p + q)
  · have hi' : p + q + 1 = i := hi
    subst i
    refine ⟨((-1 : ℤ) ^ p) • Cap.cap K p (q + 1) c.val w, ?_⟩
    have h := cap_boundary K p q c.val w
    have hc := Cohomology.Singular.Evaluation.cochainCocycle_d_eq_zero (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R))
      p (p + 1) c
    simpa only [hc, map_zero, LinearMap.zero_apply, zero_add, map_zsmul] using h.symm
  · refine ⟨0, ?_⟩
    rw [(Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).shape i (p + q) hi]
    simp

/-- Capping a cycle with a coboundary gives an explicitly witnessed boundary.
The off-shape case includes every putative incoming differential in degree zero. -/
theorem cap_coboundary_cycle_exists (K : SSet.{0}) (i p q : ℕ)
    (a : (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)).X i)
    (z : Cohomology.Singular.ChainRepresentatives.chainCycles (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K) (p + q)) :
    ∃ v : (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).X (q + 1),
      (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).d (q + 1) q v =
        Cap.cap K p q ((Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)).d i p a) z.val := by
  by_cases hip : (ComplexShape.up ℕ).Rel i p
  · have hp : i + 1 = p := hip
    subst p
    have hdeg : (i + 1) + q = i + q + 1 := by omega
    let w := Cap.chainCast K hdeg z.val
    have hw : (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).d (i + q + 1) (i + q) w = 0 := by
      change (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).d (i + q + 1) (i + q)
        (Cap.chainCast K hdeg z.val) = 0
      rw [boundary_chainCast]
      exact Cohomology.Singular.ChainRepresentatives.chainCycle_d_eq_zero (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K)
        ((i + 1) + q) (i + q) z
    have hb : Cap.chainCast K (by omega : i + q + 1 = (i + 1) + q) w = z.val :=
      chainCast_symm_apply K hdeg z.val
    have h := cap_boundary K i q a w
    rw [hw, map_zero, hb] at h
    refine ⟨- (((-1 : ℤ) ^ i) • Cap.cap K i (q + 1) a w), ?_⟩
    have heq : Cap.cap K (i + 1) q
        ((Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)).d i (i + 1) a) z.val =
        - (((-1 : ℤ) ^ i) •
          (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).d (q + 1) q (Cap.cap K i (q + 1) a w)) :=
      eq_neg_of_add_eq_zero_left h.symm
    simpa only [map_neg, map_zsmul] using heq.symm
  · refine ⟨0, ?_⟩
    rw [(Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)).shape i p hip]
    simp

/-- A fixed cocycle acts on the existing categorical simplicial homology. -/
def capCocycleHomology (K : SSet.{0}) (p q : ℕ)
    (c : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)) p) :
    (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).homology (p + q) →ₗ[R]
      (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).homology q :=
  ((Cohomology.Singular.ChainRepresentatives.chainBoundaries (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K) (p + q)).liftQ
    ((Cohomology.Singular.ChainRepresentatives.chainClass (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K) q).comp (capCycles K p q c))
    (by
      intro z hz
      rcases hz with ⟨w, rfl⟩
      change Cohomology.Singular.ChainRepresentatives.chainClass (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K) q
        (capCycles K p q c
          (Cohomology.Singular.ChainRepresentatives.chainBoundaryMap (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K) (p + q) w)) = 0
      apply (Cohomology.Singular.ChainRepresentatives.chainClass_eq_zero_iff_exists (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K) q _).mpr
      change ∃ v : (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).X (q + 1),
        (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).d (q + 1) q v =
          Cap.cap K p q c.val (((Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).sc (p + q)).f w)
      exact cap_cocycle_boundary_exists K p q c _ w)).comp
    (Cohomology.Singular.ChainRepresentatives.homologyQuotientIso (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K) (p + q)).toLinearEquiv.toLinearMap

@[simp]
theorem capCocycleHomology_chainClass (K : SSet.{0}) (p q : ℕ)
    (c : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)) p)
    (z : Cohomology.Singular.ChainRepresentatives.chainCycles (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K) (p + q)) :
    capCocycleHomology K p q c
        (Cohomology.Singular.ChainRepresentatives.chainClass (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K) (p + q) z) =
      Cohomology.Singular.ChainRepresentatives.chainClass (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K) q (capCycles K p q c z) := by
  dsimp only [capCocycleHomology, Cohomology.Singular.ChainRepresentatives.chainClass, LinearMap.comp_apply]
  simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rfl

/-- The action on homology is linear in the cocycle. -/
def cocycleCapHomology (K : SSet.{0}) (p q : ℕ) :
    Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)) p →ₗ[R]
      (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).homology (p + q) →ₗ[R]
        (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).homology q where
  toFun := capCocycleHomology K p q
  map_add' c d := by
    apply LinearMap.ext
    intro h
    obtain ⟨z, rfl⟩ := Cohomology.Singular.ChainRepresentatives.chainClass_surjective (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K) (p + q) h
    simp only [capCocycleHomology_chainClass, LinearMap.add_apply, map_add]
  map_smul' r c := by
    apply LinearMap.ext
    intro h
    obtain ⟨z, rfl⟩ := Cohomology.Singular.ChainRepresentatives.chainClass_surjective (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K) (p + q) h
    simp only [capCocycleHomology_chainClass, LinearMap.smul_apply, map_smul,
      RingHom.id_apply]

/-- A coboundary acts trivially on homology, including cochain degree zero. -/
@[simp]
theorem cocycleCapHomology_boundary (K : SSet.{0}) (p q : ℕ)
    (a : ((Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)).sc p).X₁) :
    cocycleCapHomology K p q
      (Cohomology.Singular.Representatives.cochainBoundaryMap (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)) p a) = 0 := by
  apply LinearMap.ext
  intro h
  obtain ⟨z, rfl⟩ := Cohomology.Singular.ChainRepresentatives.chainClass_surjective (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K) (p + q) h
  change capCocycleHomology K p q
    (Cohomology.Singular.Representatives.cochainBoundaryMap (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)) p a)
    (Cohomology.Singular.ChainRepresentatives.chainClass (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K) (p + q) z) = 0
  rw [capCocycleHomology_chainClass]
  apply (Cohomology.Singular.ChainRepresentatives.chainClass_eq_zero_iff_exists (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K) q _).mpr
  change ∃ v : (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).X (q + 1),
    (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).d (q + 1) q v =
      Cap.cap K p q (((Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)).sc p).f a) z.val
  exact cap_coboundary_cycle_exists K _ p q a z

/-- The actual cap product on categorical simplicial cohomology and homology. -/
def capHomology (K : SSet.{0}) (p q : ℕ) :
    (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)).homology p →ₗ[R]
      (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).homology (p + q) →ₗ[R]
        (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).homology q :=
  ((Cohomology.Singular.Representatives.cochainBoundaries (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)) p).liftQ
    (cocycleCapHomology K p q)
    (by
      intro c hc
      rcases hc with ⟨a, rfl⟩
      exact cocycleCapHomology_boundary K p q a)).comp
    (Cohomology.Singular.Representatives.cohomologyQuotientIso (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)) p).toLinearEquiv.toLinearMap

/-- On represented classes, the descended cap product is precisely the class
of the previously constructed chain-level cap product. -/
@[simp]
theorem capHomology_class_class (K : SSet.{0}) (p q : ℕ)
    (c : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)) p)
    (z : Cohomology.Singular.ChainRepresentatives.chainCycles (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K) (p + q)) :
    capHomology K p q (Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)) p c)
        (Cohomology.Singular.ChainRepresentatives.chainClass (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K) (p + q) z) =
      Cohomology.Singular.ChainRepresentatives.chainClass (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K) q (capCycles K p q c z) := by
  dsimp only [capHomology, Cohomology.Singular.Representatives.cochainClass, LinearMap.comp_apply]
  simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  exact capCocycleHomology_chainClass K p q c z

/-- Changing either representative within its actual (co)homology class does
not change the cap-product class. -/
theorem capHomology_independent (K : SSet.{0}) (p q : ℕ)
    (c c' : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)) p)
    (z z' : Cohomology.Singular.ChainRepresentatives.chainCycles (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K) (p + q))
    (hc : Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)) p c =
      Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)) p c')
    (hz : Cohomology.Singular.ChainRepresentatives.chainClass (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K) (p + q) z =
      Cohomology.Singular.ChainRepresentatives.chainClass (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K) (p + q) z') :
    Cohomology.Singular.ChainRepresentatives.chainClass (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K) q (capCycles K p q c z) =
      Cohomology.Singular.ChainRepresentatives.chainClass (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K) q (capCycles K p q c' z') := by
  rw [← capHomology_class_class, ← capHomology_class_class, hc, hz]

/-- The cap product on the actual continuous singular cohomology and homology. -/
abbrev singularCapHomology (X : TopCat.{0}) (p q : ℕ) :
    Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X p →ₗ[R]
      (Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).homology (p + q) →ₗ[R]
        (Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).homology q :=
  capHomology (TopCat.toSSet.obj X) p q

@[simp]
theorem singularCapHomology_class_class (X : TopCat.{0}) (p q : ℕ)
    (c : Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of R R) X p)
    (z : Cohomology.Singular.ChainRepresentatives.chainCycles (Cohomology.Singular.Evaluation.singularScalarChains (R := R) X) (p + q)) :
    singularCapHomology X p q (Cohomology.Singular.Representatives.singularClass (ModuleCat.of R R) X p c)
        (Cohomology.Singular.ChainRepresentatives.chainClass (Cohomology.Singular.Evaluation.singularScalarChains (R := R) X) (p + q) z) =
      Cohomology.Singular.ChainRepresentatives.chainClass (Cohomology.Singular.Evaluation.singularScalarChains (R := R) X) q
        (capCycles (TopCat.toSSet.obj X) p q c z) :=
  capHomology_class_class (TopCat.toSSet.obj X) p q c z

end

end OAI.AlgebraicTopology.Products.CapBoundary
