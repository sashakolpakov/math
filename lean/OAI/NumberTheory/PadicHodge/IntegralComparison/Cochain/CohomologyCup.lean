import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainClassNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.BilinearQuotient
import Lean.Elab.Tactic.Omega

/-! # Cohomology Cup -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cochain.CohomologyCup

noncomputable section

/-! A bilinear product obeying the graded product rule descends to the
original categorical cohomology. The boundary witnesses are constructed
explicitly in the original cochain complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainClasses

universe u v

variable {R : Type u} [CommRing R] (K : CochainComplex (ModuleCat.{v} R) ℕ)

def degreeCast {n m : ℕ} (h : n = m) : K.X n ≃ₗ[R] K.X m :=
  h ▸ LinearEquiv.refl R (K.X n)

variable (cup : ∀ n m : ℕ, K.X n →ₗ[R] K.X m →ₗ[R] K.X (n + m))

def cupInto (n m k : ℕ) (h : n + m = k) : K.X n →ₗ[R] K.X m →ₗ[R] K.X k :=
  (cup n m).compr₂ (degreeCast K h).toLinearMap

variable (leibniz : ∀ n m (x : K.X n) (y : K.X m),
  K.d (n + m) (n + m + 1) (cup n m x y) =
    cupInto K cup (n + 1) m (n + m + 1) (by omega) (K.d n (n + 1) x) y +
      (-1 : ℤ) ^ n • cupInto K cup n (m + 1) (n + m + 1) (by omega) x (K.d m (m + 1) y))

theorem degreeCast_d_target {a b c : ℕ} (h : b = c) (x : K.X a) :
    degreeCast K h (K.d a b x) = K.d a c x := by
  subst c
  rfl

theorem degreeCast_cupInto {p q a b : ℕ} (h : a = b) (hpq : p + q = a)
    (x : K.X p) (y : K.X q) :
    degreeCast K h (cupInto K cup p q a hpq x y) =
      cupInto K cup p q b (hpq.trans h) x y := by
  subst b
  rfl

include leibniz in
theorem cup_closed (p q : ℕ) (x : K.X p) (y : K.X q)
    (hx : K.d p (p + 1) x = 0) (hy : K.d q (q + 1) y = 0) :
    K.d (p + q) (p + q + 1) (cup p q x y) = 0 := by
  rw [leibniz, hx, hy, map_zero, map_zero]
  simp only [LinearMap.zero_apply, smul_zero, add_zero]

include leibniz in
theorem differential_cup_right_closed (p q k : ℕ) (hk : (p + 1) + q = k)
    (x : K.X p) (y : K.X q)
    (hy : K.d q (q + 1) y = 0) :
    K.d (p + q) k (cup p q x y) =
      cupInto K cup (p + 1) q k hk (K.d p (p + 1) x) y := by
  have h := leibniz p q x y
  rw [hy, map_zero, smul_zero, add_zero] at h
  have ht : p + q + 1 = k := by omega
  exact (degreeCast_d_target K ht _).symm.trans
    ((congrArg (degreeCast K ht) h).trans
      (degreeCast_cupInto K cup ht (by omega) _ _))

include leibniz in
theorem differential_cup_left_closed (p q k : ℕ) (hk : p + (q + 1) = k)
    (x : K.X p) (y : K.X q)
    (hx : K.d p (p + 1) x = 0) :
    K.d (p + q) k ((-1 : ℤ) ^ p • cup p q x y) =
      cupInto K cup p (q + 1) k hk x (K.d q (q + 1) y) := by
  have h := leibniz p q x y
  rw [hx, map_zero, LinearMap.zero_apply, zero_add] at h
  have hs : K.d (p + q) (p + q + 1) ((-1 : ℤ) ^ p • cup p q x y) =
      cupInto K cup p (q + 1) (p + q + 1) (by omega) x (K.d q (q + 1) y) := by
    rw [map_zsmul, h, smul_smul, ← mul_pow]
    simp only [neg_mul_neg, one_mul, one_pow, one_smul]
  have ht : p + q + 1 = k := by omega
  exact (degreeCast_d_target K ht _).symm.trans
    ((congrArg (degreeCast K ht) hs).trans
      (degreeCast_cupInto K cup ht (by omega) _ _))

def cycleCup (p q : ℕ) : Module.CochainClasses.cycles K p →ₗ[R] Module.CochainClasses.cycles K q →ₗ[R] Module.CochainClasses.cycles K (p + q) where
  toFun x :=
    { toFun := fun y => ⟨cup p q x.val y.val,
        cup_closed K cup leibniz p q x.val y.val x.property y.property⟩
      map_add' := fun y z => Subtype.ext ((cup p q x.val).map_add y.val z.val)
      map_smul' := fun r y => Subtype.ext ((cup p q x.val).map_smul r y.val) }
  map_add' x x' := by
    apply LinearMap.ext
    intro y
    exact Subtype.ext (DFunLike.congr_fun ((cup p q).map_add x.val x'.val) y.val)
  map_smul' r x := by
    apply LinearMap.ext
    intro y
    exact Subtype.ext (DFunLike.congr_fun ((cup p q).map_smul r x.val) y.val)

def cycleCupClass (p q : ℕ) : Module.CochainClasses.cycles K p →ₗ[R] Module.CochainClasses.cycles K q →ₗ[R] (K).homology (p + q) :=
  (cycleCup K cup leibniz p q).compr₂ (Module.CochainClasses.classMap K (p + q))

theorem cycleCupClass_boundary_left (p q : ℕ) (x : Module.CochainClasses.cycles K p) (y : Module.CochainClasses.cycles K q)
    (hx : x ∈ Module.CochainClasses.boundaries K p) : cycleCupClass K cup leibniz p q x y = 0 := by
  obtain ⟨b, hb⟩ := hx
  have hx0 : Module.CochainClasses.classMap K p x = 0 :=
    (Module.CochainClasses.classMap_eq_zero_iff K p x).mpr ⟨b, congrArg Subtype.val hb⟩
  cases p with
  | zero =>
      have hxz := (Module.CochainClasses.classMap_zero_eq_zero_iff K x).mp hx0
      rw [hxz, map_zero]
      rfl
  | succ p =>
      obtain ⟨z, hz⟩ := (Module.CochainClasses.classMap_succ_eq_zero_iff K p x).mp hx0
      apply (Module.CochainClasses.classMap_eq_zero_iff K ((p + 1) + q) (cycleCup K cup leibniz (p + 1) q x y)).mpr
      have hp : (ComplexShape.up ℕ).prev ((p + 1) + q) = p + q :=
        (ComplexShape.up ℕ).prev_eq' (by change p + q + 1 = (p + 1) + q; omega)
      rw [hp]
      refine ⟨cup p q z y.val, ?_⟩
      exact (differential_cup_right_closed K cup leibniz p q ((p + 1) + q) rfl z y.val y.property).trans
        (congrArg (fun w => cup (p + 1) q w y.val) hz)

theorem cycleCupClass_boundary_right (p q : ℕ) (x : Module.CochainClasses.cycles K p) (y : Module.CochainClasses.cycles K q)
    (hy : y ∈ Module.CochainClasses.boundaries K q) : cycleCupClass K cup leibniz p q x y = 0 := by
  obtain ⟨b, hb⟩ := hy
  have hy0 : Module.CochainClasses.classMap K q y = 0 :=
    (Module.CochainClasses.classMap_eq_zero_iff K q y).mpr ⟨b, congrArg Subtype.val hb⟩
  cases q with
  | zero =>
      have hyz := (Module.CochainClasses.classMap_zero_eq_zero_iff K y).mp hy0
      rw [hyz, map_zero]
  | succ q =>
      obtain ⟨z, hz⟩ := (Module.CochainClasses.classMap_succ_eq_zero_iff K q y).mp hy0
      apply (Module.CochainClasses.classMap_eq_zero_iff K (p + (q + 1)) (cycleCup K cup leibniz p (q + 1) x y)).mpr
      have hp : (ComplexShape.up ℕ).prev (p + (q + 1)) = p + q :=
        (ComplexShape.up ℕ).prev_eq' (by change p + q + 1 = p + (q + 1); omega)
      rw [hp]
      refine ⟨(-1 : ℤ) ^ p • cup p q x.val z, ?_⟩
      exact (differential_cup_left_closed K cup leibniz p q (p + (q + 1)) rfl x.val z x.property).trans
        (congrArg (fun w => cup p (q + 1) x.val w) hz)

def cohomologyCup (p q : ℕ) : (K).homology p →ₗ[R] (K).homology q →ₗ[R] (K).homology (p + q) :=
  ((BilinearQuotient.lift₂ (Module.CochainClasses.boundaries K p) (Module.CochainClasses.boundaries K q) (cycleCupClass K cup leibniz p q)
    (fun x hx y => cycleCupClass_boundary_left K cup leibniz p q x y hx)
    (fun x y hy => cycleCupClass_boundary_right K cup leibniz p q x y hy)).comp
      (Module.CochainClasses.quotientIso K p).hom.hom).compl₂ (Module.CochainClasses.quotientIso K q).hom.hom

theorem quotient_classMap (p : ℕ) (x : Module.CochainClasses.cycles K p) :
    (Module.CochainClasses.quotientIso K p).hom (Module.CochainClasses.classMap K p x) = (Module.CochainClasses.boundaries K p).mkQ x :=
  ConcreteCategory.congr_hom (Module.CochainClasses.quotientIso K p).inv_hom_id ((Module.CochainClasses.boundaries K p).mkQ x)

theorem cup_class (p q : ℕ) (x : Module.CochainClasses.cycles K p) (y : Module.CochainClasses.cycles K q) :
    cohomologyCup K cup leibniz p q (Module.CochainClasses.classMap K p x) (Module.CochainClasses.classMap K q y) =
      Module.CochainClasses.classMap K (p + q) (cycleCup K cup leibniz p q x y) := by
  change BilinearQuotient.lift₂ (Module.CochainClasses.boundaries K p) (Module.CochainClasses.boundaries K q)
    (cycleCupClass K cup leibniz p q)
    (fun x hx y => cycleCupClass_boundary_left K cup leibniz p q x y hx)
    (fun x y hy => cycleCupClass_boundary_right K cup leibniz p q x y hy)
    ((Module.CochainClasses.quotientIso K p).hom (Module.CochainClasses.classMap K p x)) ((Module.CochainClasses.quotientIso K q).hom (Module.CochainClasses.classMap K q y)) = _
  rw [quotient_classMap, quotient_classMap, BilinearQuotient.lift₂_mkQ]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cochain.CohomologyCup
