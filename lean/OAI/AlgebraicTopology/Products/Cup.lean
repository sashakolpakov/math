import OAI.AlgebraicTopology.Products.SimplexFaceIdentities
import OAI.AlgebraicTopology.Cohomology.Singular.Formulas
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Abel

/-! # Cup -/

namespace OAI.AlgebraicTopology.Products.Cup

noncomputable section

section

/-!
# The cup product on genuine simplicial cochains

The product below evaluates on a simplex by applying a bilinear coefficient
pairing to the cochains evaluated on its front and back faces. Its differential
identity is proved from the actual alternating-face differential. Specializing
to the singular simplicial set gives the ordinary singular cup product.
-/

open _root_.CategoryTheory Opposite
open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex Simplicial
open OAI.AlgebraicTopology.Cohomology.Singular.Formulas

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [CommRing R]

/-- Cochain equality can be checked on every simplex. -/
theorem cochain_ext (K : SSet.{0}) (M : ModuleCat.{0} R) {n : ℕ}
    {c d : (Cohomology.Singular.Basic.simplicialCochains K M).X n}
    (h : ∀ s : K _⦋n⦌, Cohomology.Singular.Coefficients.simplicialEvaluation K M s c = Cohomology.Singular.Coefficients.simplicialEvaluation K M s d) :
    c = d := by
  apply (Cohomology.Singular.Coefficients.degreewiseFunctionIso K M n).toLinearEquiv.injective
  funext s
  change (Cohomology.Singular.Coefficients.degreewiseFunctionIso K M n).hom c s = (Cohomology.Singular.Coefficients.degreewiseFunctionIso K M n).hom d s
  exact (Cohomology.Singular.Coefficients.degreewiseFunctionIso_hom_apply K M c s).trans
    ((h s).trans (Cohomology.Singular.Coefficients.degreewiseFunctionIso_hom_apply K M d s).symm)

/-- Linear transport of cochains along an equality of degrees. -/
def cochainCast (K : SSet.{0}) (M : ModuleCat.{0} R) {m n : ℕ} (h : m = n) :
    (Cohomology.Singular.Basic.simplicialCochains K M).X m →ₗ[R] (Cohomology.Singular.Basic.simplicialCochains K M).X n := by
  subst n
  exact LinearMap.id

@[simp]
theorem cochainCast_rfl (K : SSet.{0}) (M : ModuleCat.{0} R) {n : ℕ}
    (c : (Cohomology.Singular.Basic.simplicialCochains K M).X n) : cochainCast K M rfl c = c := rfl

@[simp]
theorem evaluation_cochainCast (K : SSet.{0}) (M : ModuleCat.{0} R)
    {m n : ℕ} (h : m = n) (c : (Cohomology.Singular.Basic.simplicialCochains K M).X m) (s : K _⦋n⦌) :
    Cohomology.Singular.Coefficients.simplicialEvaluation K M s (cochainCast K M h c) =
      Cohomology.Singular.Coefficients.simplicialEvaluation K M (SimplexFaceIdentities.simplexCast K h.symm s) c := by
  subst n
  rfl

@[simp]
theorem evaluation_cochainCast_simplexCast (K : SSet.{0}) (M : ModuleCat.{0} R)
    {m n : ℕ} (h : m = n) (c : (Cohomology.Singular.Basic.simplicialCochains K M).X m) (s : K _⦋m⦌) :
    Cohomology.Singular.Coefficients.simplicialEvaluation K M (SimplexFaceIdentities.simplexCast K h s) (cochainCast K M h c) =
      Cohomology.Singular.Coefficients.simplicialEvaluation K M s c := by
  subst n
  rfl

/-- The front/back cup pairing associated to any bilinear coefficient map. -/
def cupWith (K : SSet.{0}) {M N L : ModuleCat.{0} R}
    (B : M →ₗ[R] N →ₗ[R] L) {p q : ℕ}
    (c : (Cohomology.Singular.Basic.simplicialCochains K M).X p) (d : (Cohomology.Singular.Basic.simplicialCochains K N).X q) :
    (Cohomology.Singular.Basic.simplicialCochains K L).X (p + q) :=
  (Cohomology.Singular.Coefficients.degreewiseFunctionIso K L (p + q)).toLinearEquiv.symm
    (fun s => B (Cohomology.Singular.Coefficients.simplicialEvaluation K M (SimplexFaceIdentities.frontFace K p q s) c)
      (Cohomology.Singular.Coefficients.simplicialEvaluation K N (SimplexFaceIdentities.backFace K p q s) d))

@[simp]
theorem evaluation_cupWith (K : SSet.{0}) {M N L : ModuleCat.{0} R}
    (B : M →ₗ[R] N →ₗ[R] L) {p q : ℕ}
    (c : (Cohomology.Singular.Basic.simplicialCochains K M).X p) (d : (Cohomology.Singular.Basic.simplicialCochains K N).X q)
    (s : K _⦋p + q⦌) :
    Cohomology.Singular.Coefficients.simplicialEvaluation K L s (cupWith K B c d) =
      B (Cohomology.Singular.Coefficients.simplicialEvaluation K M (SimplexFaceIdentities.frontFace K p q s) c)
        (Cohomology.Singular.Coefficients.simplicialEvaluation K N (SimplexFaceIdentities.backFace K p q s) d) := by
  rw [← Cohomology.Singular.Coefficients.degreewiseFunctionIso_hom_apply]
  change ((Cohomology.Singular.Coefficients.degreewiseFunctionIso K L (p + q)).toLinearEquiv
    ((Cohomology.Singular.Coefficients.degreewiseFunctionIso K L (p + q)).toLinearEquiv.symm _)) s = _
  rw [LinearEquiv.apply_symm_apply]

theorem cupWith_add_left (K : SSet.{0}) {M N L : ModuleCat.{0} R}
    (B : M →ₗ[R] N →ₗ[R] L) {p q : ℕ}
    (c c' : (Cohomology.Singular.Basic.simplicialCochains K M).X p) (d : (Cohomology.Singular.Basic.simplicialCochains K N).X q) :
    cupWith K B (c + c') d = cupWith K B c d + cupWith K B c' d := by
  apply cochain_ext K L
  intro s
  simp only [evaluation_cupWith, map_add, LinearMap.add_apply]

theorem cupWith_add_right (K : SSet.{0}) {M N L : ModuleCat.{0} R}
    (B : M →ₗ[R] N →ₗ[R] L) {p q : ℕ}
    (c : (Cohomology.Singular.Basic.simplicialCochains K M).X p) (d d' : (Cohomology.Singular.Basic.simplicialCochains K N).X q) :
    cupWith K B c (d + d') = cupWith K B c d + cupWith K B c d' := by
  apply cochain_ext K L
  intro s
  simp only [evaluation_cupWith, map_add]

theorem cupWith_smul_left (K : SSet.{0}) {M N L : ModuleCat.{0} R}
    (B : M →ₗ[R] N →ₗ[R] L) {p q : ℕ} (r : R)
    (c : (Cohomology.Singular.Basic.simplicialCochains K M).X p) (d : (Cohomology.Singular.Basic.simplicialCochains K N).X q) :
    cupWith K B (r • c) d = r • cupWith K B c d := by
  apply cochain_ext K L
  intro s
  simp only [evaluation_cupWith, map_smul, LinearMap.smul_apply]

theorem cupWith_smul_right (K : SSet.{0}) {M N L : ModuleCat.{0} R}
    (B : M →ₗ[R] N →ₗ[R] L) {p q : ℕ} (r : R)
    (c : (Cohomology.Singular.Basic.simplicialCochains K M).X p) (d : (Cohomology.Singular.Basic.simplicialCochains K N).X q) :
    cupWith K B c (r • d) = r • cupWith K B c d := by
  apply cochain_ext K L
  intro s
  simp only [evaluation_cupWith, map_smul]

@[simp]
theorem cupWith_zero_left (K : SSet.{0}) {M N L : ModuleCat.{0} R}
    (B : M →ₗ[R] N →ₗ[R] L) {p q : ℕ} (d : (Cohomology.Singular.Basic.simplicialCochains K N).X q) :
    cupWith K B (0 : (Cohomology.Singular.Basic.simplicialCochains K M).X p) d = 0 := by
  apply cochain_ext K L
  intro s
  simp only [evaluation_cupWith, map_zero, LinearMap.zero_apply]

@[simp]
theorem cupWith_zero_right (K : SSet.{0}) {M N L : ModuleCat.{0} R}
    (B : M →ₗ[R] N →ₗ[R] L) {p q : ℕ} (c : (Cohomology.Singular.Basic.simplicialCochains K M).X p) :
    cupWith K B c (0 : (Cohomology.Singular.Basic.simplicialCochains K N).X q) = 0 := by
  apply cochain_ext K L
  intro s
  simp only [evaluation_cupWith, map_zero]

/-- The cup operation is bilinear on the actual cochain objects. -/
def cupWithBilinear (K : SSet.{0}) {M N L : ModuleCat.{0} R}
    (B : M →ₗ[R] N →ₗ[R] L) (p q : ℕ) :
    (Cohomology.Singular.Basic.simplicialCochains K M).X p →ₗ[R]
      (Cohomology.Singular.Basic.simplicialCochains K N).X q →ₗ[R] (Cohomology.Singular.Basic.simplicialCochains K L).X (p + q) where
  toFun c :=
    { toFun := cupWith K B c
      map_add' := cupWith_add_right K B c
      map_smul' := fun r d => cupWith_smul_right K B r c d }
  map_add' c c' := by
    apply LinearMap.ext
    exact cupWith_add_left K B c c'
  map_smul' r c := by
    apply LinearMap.ext
    exact cupWith_smul_left K B r c

@[simp]
theorem cupWithBilinear_apply (K : SSet.{0}) {M N L : ModuleCat.{0} R}
    (B : M →ₗ[R] N →ₗ[R] L) {p q : ℕ}
    (c : (Cohomology.Singular.Basic.simplicialCochains K M).X p) (d : (Cohomology.Singular.Basic.simplicialCochains K N).X q) :
    cupWithBilinear K B p q c d = cupWith K B c d := rfl

/-- Cancellation of the shared middle face in the cup-product differential. -/
theorem alternatingCupSum {V : Type*} [AddCommGroup V] (p q : ℕ)
    (a : Fin (p + 2) → V) (b : Fin (q + 2) → V)
    (h : a (Fin.last (p + 1)) = b 0) :
    (∑ i : Fin (p + 1), (-1 : ℤ) ^ i.val • a i.castSucc) +
        (∑ j : Fin (q + 1), (-1 : ℤ) ^ (p + 1 + j.val) • b j.succ) =
      (∑ i : Fin (p + 2), (-1 : ℤ) ^ i.val • a i) +
        (-1 : ℤ) ^ p • (∑ j : Fin (q + 2), (-1 : ℤ) ^ j.val • b j) := by
  rw [Fin.sum_univ_castSucc (fun i : Fin (p + 2) => (-1 : ℤ) ^ i.val • a i),
    Fin.sum_univ_succ (fun j : Fin (q + 2) => (-1 : ℤ) ^ j.val • b j)]
  simp only [Fin.val_castSucc, Fin.val_last, Fin.val_zero, Fin.val_succ,
    pow_zero, one_smul]
  rw [smul_add, Finset.smul_sum]
  simp_rw [smul_smul, ← pow_add]
  have hs : (∑ j : Fin (q + 1), (-1 : ℤ) ^ (p + (j.val + 1)) • b j.succ) =
      ∑ j : Fin (q + 1), (-1 : ℤ) ^ (p + 1 + j.val) • b j.succ := by
    simp only [Nat.add_assoc, Nat.add_comm 1]
  rw [hs, h, pow_succ]
  simp only [mul_neg_one, neg_smul]
  abel

/-- Cochain cup product with multiplication of scalar coefficients. -/
def cup (K : SSet.{0}) {p q : ℕ}
    (c : (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)).X p)
    (d : (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)).X q) :
    (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)).X (p + q) :=
  cupWith K (LinearMap.mul R R) c d

/-- The ordinary cup product on the genuine singular cochain complex. -/
abbrev singularCup (X : TopCat.{0}) {p q : ℕ}
    (c : (Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).X p)
    (d : (Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).X q) :
    (Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).X (p + q) :=
  cup (TopCat.toSSet.obj X) c d

/-- The Leibniz rule for the genuine cochain differential and any bilinear cup pairing. -/
theorem cupWith_coboundary (K : SSet.{0}) {M N L : ModuleCat.{0} R}
    (B : M →ₗ[R] N →ₗ[R] L) {p q : ℕ}
    (c : (Cohomology.Singular.Basic.simplicialCochains K M).X p) (d : (Cohomology.Singular.Basic.simplicialCochains K N).X q) :
    (Cohomology.Singular.Basic.simplicialCochains K L).d (p + q) (p + q + 1) (cupWith K B c d) =
      cochainCast K L (by omega : (p + 1) + q = p + q + 1)
        (cupWith K B ((Cohomology.Singular.Basic.simplicialCochains K M).d p (p + 1) c) d) +
      (-1 : ℤ) ^ p • cupWith K B c ((Cohomology.Singular.Basic.simplicialCochains K N).d q (q + 1) d) := by
  apply cochain_ext K L
  intro s
  simp only [map_add, map_zsmul, evaluation_cochainCast, evaluation_cupWith,
    Cohomology.Singular.Formulas.evaluation_coboundary_apply, map_sum, LinearMap.sum_apply, LinearMap.smul_apply]
  erw [evaluation_cupWith K B (p := p) (q := q + 1) c
    ((Cohomology.Singular.Basic.simplicialCochains K N).d q (q + 1) d) s]
  simp only [Cohomology.Singular.Formulas.evaluation_coboundary_apply, map_sum, map_zsmul]
  rw [SimplexFaceIdentities.sum_face_split p q]
  simp only [SimplexFaceIdentities.leftFaceIndex_val, SimplexFaceIdentities.rightFaceIndex_val, SimplexFaceIdentities.frontFace_delta_left,
    SimplexFaceIdentities.backFace_delta_left, SimplexFaceIdentities.frontFace_delta_right, SimplexFaceIdentities.backFace_delta_right]
  refine alternatingCupSum (V := L) p q
    (fun i => B
      (Cohomology.Singular.Coefficients.simplicialEvaluation K M (K.δ i (SimplexFaceIdentities.frontFace K (p + 1) q
        (SimplexFaceIdentities.simplexCast K (by omega : p + q + 1 = (p + 1) + q) s))) c)
      (Cohomology.Singular.Coefficients.simplicialEvaluation K N (SimplexFaceIdentities.backFace K (p + 1) q
        (SimplexFaceIdentities.simplexCast K (by omega : p + q + 1 = (p + 1) + q) s)) d))
    (fun j => B
      (Cohomology.Singular.Coefficients.simplicialEvaluation K M (SimplexFaceIdentities.frontFace K p (q + 1) s) c)
      (Cohomology.Singular.Coefficients.simplicialEvaluation K N (K.δ j (SimplexFaceIdentities.backFace K p (q + 1) s)) d)) ?_
  rw [SimplexFaceIdentities.frontFace_delta_last, SimplexFaceIdentities.backFace_delta_zero]

theorem cupWith_pullback {K J : SSet.{0}} (f : K ⟶ J)
    {M N L : ModuleCat.{0} R} (B : M →ₗ[R] N →ₗ[R] L) {p q : ℕ}
    (c : (Cohomology.Singular.Basic.simplicialCochains J M).X p) (d : (Cohomology.Singular.Basic.simplicialCochains J N).X q) :
    (Cohomology.Singular.Functor.simplicialPullback L f).f (p + q) (cupWith J B c d) =
      cupWith K B ((Cohomology.Singular.Functor.simplicialPullback M f).f p c) ((Cohomology.Singular.Functor.simplicialPullback N f).f q d) := by
  apply cochain_ext K L
  intro s
  simp only [Cohomology.Singular.Formulas.evaluation_pullback_apply, evaluation_cupWith,
    SimplexFaceIdentities.frontFace_naturality, SimplexFaceIdentities.backFace_naturality]

/-- The cup pairing of two actual cocycles is an actual cocycle. -/
theorem cupWith_cocycles (K : SSet.{0}) {M N L : ModuleCat.{0} R}
    (B : M →ₗ[R] N →ₗ[R] L) {p q : ℕ}
    (c : (Cohomology.Singular.Basic.simplicialCochains K M).X p) (d : (Cohomology.Singular.Basic.simplicialCochains K N).X q)
    (hc : (Cohomology.Singular.Basic.simplicialCochains K M).d p (p + 1) c = 0)
    (hd : (Cohomology.Singular.Basic.simplicialCochains K N).d q (q + 1) d = 0) :
    (Cohomology.Singular.Basic.simplicialCochains K L).d (p + q) (p + q + 1) (cupWith K B c d) = 0 := by
  rw [cupWith_coboundary, hc, hd, cupWith_zero_left, cupWith_zero_right,
    map_zero, smul_zero, add_zero]

/-- Scalar cup product is multiplication of front and back face evaluations. -/
@[simp]
theorem evaluation_cup (K : SSet.{0}) {p q : ℕ}
    (c : (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)).X p)
    (d : (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)).X q) (s : K _⦋p + q⦌) :
    Cohomology.Singular.Coefficients.simplicialEvaluation K (ModuleCat.of R R) s (cup K c d) =
      Cohomology.Singular.Coefficients.simplicialEvaluation K (ModuleCat.of R R) (SimplexFaceIdentities.frontFace K p q s) c *
        Cohomology.Singular.Coefficients.simplicialEvaluation K (ModuleCat.of R R) (SimplexFaceIdentities.backFace K p q s) d := by
  unfold cup
  exact evaluation_cupWith K (M := ModuleCat.of R R) (N := ModuleCat.of R R)
    (L := ModuleCat.of R R) (LinearMap.mul R R) c d s

/-- On continuous singular simplices, the product uses the ordinary front and back inclusions. -/
theorem singularCup_continuous_evaluation (X : TopCat.{0}) {p q : ℕ}
    (c : (Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).X p)
    (d : (Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).X q)
    (s : C(Convexity.StdSimplex ℝ (Fin (p + q + 1)), X)) :
    (Cohomology.Singular.Coefficients.singularDegreewiseContinuousFunctionIso (ModuleCat.of R R) X (p + q)).hom
        (singularCup X c d) s =
      (Cohomology.Singular.Coefficients.singularDegreewiseContinuousFunctionIso (ModuleCat.of R R) X p).hom c
        (s.comp (SimplexFaceIdentities.standardSimplexInterval 0 p (by omega))) *
      (Cohomology.Singular.Coefficients.singularDegreewiseContinuousFunctionIso (ModuleCat.of R R) X q).hom d
        (s.comp (SimplexFaceIdentities.standardSimplexInterval p q le_rfl)) := by
  have front : SimplexFaceIdentities.frontFace (TopCat.toSSet.obj X) p q
      ((Cohomology.Singular.Coefficients.singularSimplicesEquivContinuousMap X (p + q)).symm s) =
      (Cohomology.Singular.Coefficients.singularSimplicesEquivContinuousMap X p).symm
        (s.comp (SimplexFaceIdentities.standardSimplexInterval 0 p (by omega))) := by
    apply (Cohomology.Singular.Coefficients.singularSimplicesEquivContinuousMap X p).injective
    simpa only [Cohomology.Singular.Coefficients.singularSimplicesEquivContinuousMap, SimplexFaceIdentities.frontFace,
      Equiv.apply_symm_apply] using SimplexFaceIdentities.intervalFace_continuousMap X 0 p (by omega)
        ((Cohomology.Singular.Coefficients.singularSimplicesEquivContinuousMap X (p + q)).symm s)
  have back : SimplexFaceIdentities.backFace (TopCat.toSSet.obj X) p q
      ((Cohomology.Singular.Coefficients.singularSimplicesEquivContinuousMap X (p + q)).symm s) =
      (Cohomology.Singular.Coefficients.singularSimplicesEquivContinuousMap X q).symm
        (s.comp (SimplexFaceIdentities.standardSimplexInterval p q le_rfl)) := by
    apply (Cohomology.Singular.Coefficients.singularSimplicesEquivContinuousMap X q).injective
    simpa only [Cohomology.Singular.Coefficients.singularSimplicesEquivContinuousMap, SimplexFaceIdentities.backFace,
      Equiv.apply_symm_apply] using SimplexFaceIdentities.intervalFace_continuousMap X p q le_rfl
        ((Cohomology.Singular.Coefficients.singularSimplicesEquivContinuousMap X (p + q)).symm s)
  have heval {n : ℕ} (u : (Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).X n)
      (t : C(Convexity.StdSimplex ℝ (Fin (n + 1)), X)) :
      (Cohomology.Singular.Coefficients.singularDegreewiseContinuousFunctionIso (ModuleCat.of R R) X n).hom u t =
        Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj X) (ModuleCat.of R R)
          ((Cohomology.Singular.Coefficients.singularSimplicesEquivContinuousMap X n).symm t) u :=
    (Cohomology.Singular.ContinuousFormulas.singularDegreewiseContinuousFunctionIso_hom_apply (ModuleCat.of R R) X u t).trans
      (Cohomology.Singular.Coefficients.degreewiseFunctionIso_hom_apply (TopCat.toSSet.obj X) (ModuleCat.of R R) u _)
  rw [heval (singularCup X c d) s, heval c _, heval d _]
  rw [evaluation_cup, front, back]

end

/-!
# Associativity and units of the actual cochain cup product

Composing the front and back restrictions is computed in the simplex category.
The resulting identities prove strict associativity of the Alexander--Whitney
cup product, with the equality of degree sums recorded by the existing linear
cochain transport. The unit is the actual constant-one cochain in degree zero.
-/

open _root_.CategoryTheory Opposite
open scoped Simplicial
open OAI.AlgebraicTopology.Cohomology.Singular.Formulas

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Composition of two consecutive vertex inclusions adds their offsets. -/
theorem subinterval_comp {p m n : ℕ} (a b : ℕ)
    (ha : a + p ≤ m) (hb : b + m ≤ n) :
    SimplexCategory.subinterval a p ha ≫ SimplexCategory.subinterval b m hb =
      SimplexCategory.subinterval (b + a) p (by omega : b + a + p ≤ n) := by
  ext k
  change k.val + a + b = k.val + (b + a)
  omega

/-- The interval containing all vertices is the identity in the simplex category. -/
theorem subinterval_zero_self (n : ℕ) :
    SimplexCategory.subinterval 0 n (by omega : 0 + n ≤ n) = 𝟙 ⦋n⦌ := by
  ext k
  change k.val + 0 = k.val
  exact Nat.add_zero _

/-- Restricting to two successive intervals is restriction to the resulting interval. -/
theorem intervalFace_comp (K : SSet.{0}) {p m n : ℕ} (a b : ℕ)
    (ha : a + p ≤ m) (hb : b + m ≤ n) (s : K _⦋n⦌) :
    SimplexFaceIdentities.intervalFace K a p ha (SimplexFaceIdentities.intervalFace K b m hb s) =
      SimplexFaceIdentities.intervalFace K (b + a) p (by omega : b + a + p ≤ n) s := by
  simpa only [SimplexFaceIdentities.intervalFace, op_comp, Functor.map_comp, types_comp_apply] using
    congrArg (fun f : ⦋p⦌ ⟶ ⦋n⦌ => K.map f.op s) (subinterval_comp a b ha hb)

/-- Restricting a simplex to all its vertices leaves it unchanged. -/
@[simp]
theorem intervalFace_zero_self (K : SSet.{0}) {n : ℕ} (s : K _⦋n⦌) :
    SimplexFaceIdentities.intervalFace K 0 n (by omega : 0 + n ≤ n) s = s := by
  simpa only [SimplexFaceIdentities.intervalFace, subinterval_zero_self, op_id] using K.map_id_apply (op ⦋n⦌) s

/-- The iterated front restriction used on the two sides of associativity agrees. -/
theorem frontFace_frontFace (K : SSet.{0}) (p q r : ℕ) (s : K _⦋p + (q + r)⦌) :
    SimplexFaceIdentities.frontFace K p q (SimplexFaceIdentities.frontFace K (p + q) r
      (SimplexFaceIdentities.simplexCast K (Nat.add_assoc p q r).symm s)) = SimplexFaceIdentities.frontFace K p (q + r) s := by
  simp only [SimplexFaceIdentities.frontFace, SimplexFaceIdentities.intervalFace_simplexCast, intervalFace_comp, Nat.zero_add]

/-- The two ways of extracting the middle block of vertices agree. -/
theorem backFace_frontFace (K : SSet.{0}) (p q r : ℕ) (s : K _⦋p + (q + r)⦌) :
    SimplexFaceIdentities.backFace K p q (SimplexFaceIdentities.frontFace K (p + q) r
      (SimplexFaceIdentities.simplexCast K (Nat.add_assoc p q r).symm s)) =
        SimplexFaceIdentities.frontFace K q r (SimplexFaceIdentities.backFace K p (q + r) s) := by
  simp only [SimplexFaceIdentities.frontFace, SimplexFaceIdentities.backFace, SimplexFaceIdentities.intervalFace_simplexCast, intervalFace_comp,
    Nat.zero_add, Nat.add_zero]

/-- The iterated back restriction is restriction to the last block of vertices. -/
theorem backFace_backFace (K : SSet.{0}) (p q r : ℕ) (s : K _⦋p + (q + r)⦌) :
    SimplexFaceIdentities.backFace K q r (SimplexFaceIdentities.backFace K p (q + r) s) =
      SimplexFaceIdentities.backFace K (p + q) r (SimplexFaceIdentities.simplexCast K (Nat.add_assoc p q r).symm s) := by
  simp only [SimplexFaceIdentities.backFace, SimplexFaceIdentities.intervalFace_simplexCast, intervalFace_comp]

@[simp]
theorem frontFace_zero_right (K : SSet.{0}) {p : ℕ} (s : K _⦋p⦌) :
    SimplexFaceIdentities.frontFace K p 0 s = s := intervalFace_zero_self K s

@[simp]
theorem backFace_zero_left (K : SSet.{0}) {p : ℕ} (s : K _⦋p⦌) :
    SimplexFaceIdentities.backFace K 0 p (SimplexFaceIdentities.simplexCast K (Nat.zero_add p).symm s) = s := by
  simp only [SimplexFaceIdentities.backFace, SimplexFaceIdentities.intervalFace_simplexCast, intervalFace_zero_self]

variable {R : Type} [CommRing R]

/-- Associative coefficient pairings give associative products of actual cochains. -/
theorem cupWith_assoc (K : SSet.{0})
    {M N L P Q T : ModuleCat.{0} R}
    (B₁ : M →ₗ[R] N →ₗ[R] P) (B₂ : P →ₗ[R] L →ₗ[R] T)
    (B₃ : N →ₗ[R] L →ₗ[R] Q) (B₄ : M →ₗ[R] Q →ₗ[R] T)
    (hB : ∀ (x : M) (y : N) (z : L), B₂ (B₁ x y) z = B₄ x (B₃ y z))
    {p q r : ℕ} (a : (Cohomology.Singular.Basic.simplicialCochains K M).X p)
    (b : (Cohomology.Singular.Basic.simplicialCochains K N).X q) (c : (Cohomology.Singular.Basic.simplicialCochains K L).X r) :
    cochainCast K T (Nat.add_assoc p q r) (cupWith K B₂ (cupWith K B₁ a b) c) =
      cupWith K B₄ a (cupWith K B₃ b c) := by
  apply cochain_ext K T
  intro s
  simp only [evaluation_cochainCast, evaluation_cupWith,
    frontFace_frontFace, backFace_frontFace, backFace_backFace]
  exact hB _ _ _

/-- The ordinary scalar cup product is associative, with its degree transport explicit. -/
theorem cup_assoc (K : SSet.{0}) {p q r : ℕ}
    (a : (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)).X p)
    (b : (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)).X q)
    (c : (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)).X r) :
    cochainCast K (ModuleCat.of R R) (Nat.add_assoc p q r) (cup K (cup K a b) c) =
      cup K a (cup K b c) := by
  exact cupWith_assoc K
    (M := ModuleCat.of R R) (N := ModuleCat.of R R) (L := ModuleCat.of R R)
    (P := ModuleCat.of R R) (Q := ModuleCat.of R R) (T := ModuleCat.of R R)
    (LinearMap.mul R R) (LinearMap.mul R R) (LinearMap.mul R R) (LinearMap.mul R R)
    (fun x y z => mul_assoc x y z) a b c

/-- The degree-zero cochain taking the value one on every vertex. -/
def cupUnit (K : SSet.{0}) : (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)).X 0 :=
  (Cohomology.Singular.Coefficients.degreewiseFunctionIso K (ModuleCat.of R R) 0).toLinearEquiv.symm (fun _ => 1)

@[simp]
theorem evaluation_cupUnit (K : SSet.{0}) (s : K _⦋0⦌) :
    Cohomology.Singular.Coefficients.simplicialEvaluation K (ModuleCat.of R R) s (cupUnit K) = 1 := by
  rw [← Cohomology.Singular.Coefficients.degreewiseFunctionIso_hom_apply]
  change ((Cohomology.Singular.Coefficients.degreewiseFunctionIso K (ModuleCat.of R R) 0).toLinearEquiv
    ((Cohomology.Singular.Coefficients.degreewiseFunctionIso K (ModuleCat.of R R) 0).toLinearEquiv.symm (fun _ => 1))) s = 1
  rw [LinearEquiv.apply_symm_apply]

/-- The constant-one cochain is a left unit after identifying `0 + p` with `p`. -/
theorem cupUnit_cup (K : SSet.{0}) {p : ℕ}
    (c : (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)).X p) :
    cochainCast K (ModuleCat.of R R) (Nat.zero_add p) (cup K (cupUnit K) c) = c := by
  apply cochain_ext K (ModuleCat.of R R)
  intro s
  let t := SimplexFaceIdentities.simplexCast K (Nat.zero_add p).symm s
  calc
    _ = Cohomology.Singular.Coefficients.simplicialEvaluation K (ModuleCat.of R R) t (cup K (cupUnit K) c) :=
      evaluation_cochainCast K (ModuleCat.of R R) (Nat.zero_add p) _ s
    _ = Cohomology.Singular.Coefficients.simplicialEvaluation K (ModuleCat.of R R) (SimplexFaceIdentities.frontFace K 0 p t) (cupUnit K) *
        Cohomology.Singular.Coefficients.simplicialEvaluation K (ModuleCat.of R R) (SimplexFaceIdentities.backFace K 0 p t) c :=
      evaluation_cupWith K (M := ModuleCat.of R R) (N := ModuleCat.of R R)
        (L := ModuleCat.of R R) (LinearMap.mul R R) (cupUnit K) c t
    _ = 1 * Cohomology.Singular.Coefficients.simplicialEvaluation K (ModuleCat.of R R) s c := by
      rw [evaluation_cupUnit (R := R) K (SimplexFaceIdentities.frontFace K 0 p t), backFace_zero_left K s]
    _ = _ := one_mul _

/-- The constant-one cochain is a right unit. -/
@[simp]
theorem cup_cupUnit (K : SSet.{0}) {p : ℕ}
    (c : (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)).X p) :
    cup K c (cupUnit K) = c := by
  apply cochain_ext K (ModuleCat.of R R)
  intro s
  calc
    _ = Cohomology.Singular.Coefficients.simplicialEvaluation K (ModuleCat.of R R) (SimplexFaceIdentities.frontFace K p 0 s) c *
        Cohomology.Singular.Coefficients.simplicialEvaluation K (ModuleCat.of R R) (SimplexFaceIdentities.backFace K p 0 s) (cupUnit K) :=
      evaluation_cupWith K (M := ModuleCat.of R R) (N := ModuleCat.of R R)
        (L := ModuleCat.of R R) (LinearMap.mul R R) c (cupUnit K) s
    _ = Cohomology.Singular.Coefficients.simplicialEvaluation K (ModuleCat.of R R) s c * 1 := by
      exact congrArg₂ (fun x y : R => x * y)
        (congrArg (fun t : K _⦋p⦌ => Cohomology.Singular.Coefficients.simplicialEvaluation K (ModuleCat.of R R) t c)
          (frontFace_zero_right K (p := p) s))
        (evaluation_cupUnit (R := R) K (SimplexFaceIdentities.backFace K p 0 s))
    _ = _ := mul_one _

/-- The cochain unit is closed for the actual alternating-face differential. -/
@[simp]
theorem cupUnit_coboundary (K : SSet.{0}) :
    (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)).d 0 1 (cupUnit K) = 0 := by
  apply cochain_ext K (ModuleCat.of R R)
  intro s
  simp only [map_zero]
  calc
    _ = ∑ i : Fin 2, (-1 : ℤ) ^ i.val •
        Cohomology.Singular.Coefficients.simplicialEvaluation K (ModuleCat.of R R) (K.δ i s) (cupUnit K) :=
      Cohomology.Singular.Formulas.evaluation_coboundary_apply K (ModuleCat.of R R) (n := 0) (cupUnit K) s
    _ = ∑ i : Fin 2, (-1 : ℤ) ^ i.val • (1 : R) := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun r : R => (-1 : ℤ) ^ i.val • r)
        (evaluation_cupUnit (R := R) K (K.δ i s))
    _ = 0 := by simp [Fin.sum_univ_two]

/-- Pullback preserves the actual unit cochain. -/
@[simp]
theorem cupUnit_pullback {K L : SSet.{0}} (f : K ⟶ L) :
    (Cohomology.Singular.Functor.simplicialPullback (ModuleCat.of R R) f).f 0 (cupUnit L) = cupUnit K := by
  apply cochain_ext K (ModuleCat.of R R)
  intro s
  calc
    _ = Cohomology.Singular.Coefficients.simplicialEvaluation L (ModuleCat.of R R) (f.app _ s) (cupUnit L) :=
      Cohomology.Singular.Formulas.evaluation_pullback_apply (ModuleCat.of R R) f (cupUnit L) s
    _ = 1 := evaluation_cupUnit (R := R) L (f.app _ s)
    _ = _ := (evaluation_cupUnit (R := R) K s).symm

/-- The unit of the genuine singular cochain cup product. -/
abbrev singularCupUnit (X : TopCat.{0}) :
    (Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).X 0 := cupUnit (TopCat.toSSet.obj X)

/-- Associativity on genuine singular cochains. -/
theorem singularCup_assoc (X : TopCat.{0}) {p q r : ℕ}
    (a : (Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).X p)
    (b : (Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).X q)
    (c : (Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).X r) :
    cochainCast (TopCat.toSSet.obj X) (ModuleCat.of R R) (Nat.add_assoc p q r)
      (singularCup X (singularCup X a b) c) = singularCup X a (singularCup X b c) :=
  cup_assoc (TopCat.toSSet.obj X) a b c

/-- The left unit law on genuine singular cochains. -/
theorem singularCupUnit_cup (X : TopCat.{0}) {p : ℕ}
    (c : (Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).X p) :
    cochainCast (TopCat.toSSet.obj X) (ModuleCat.of R R) (Nat.zero_add p)
      (singularCup X (singularCupUnit X) c) = c :=
  cupUnit_cup (TopCat.toSSet.obj X) c

/-- The right unit law on genuine singular cochains. -/
@[simp]
theorem singularCup_cupUnit (X : TopCat.{0}) {p : ℕ}
    (c : (Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).X p) :
    singularCup X c (singularCupUnit X) = c := cup_cupUnit (TopCat.toSSet.obj X) c

/-- The singular cochain unit represents a degree-zero cohomology class. -/
@[simp]
theorem singularCupUnit_coboundary (X : TopCat.{0}) :
    (Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).d 0 1 (singularCupUnit X) = 0 :=
  cupUnit_coboundary (TopCat.toSSet.obj X)

end

end OAI.AlgebraicTopology.Products.Cup
