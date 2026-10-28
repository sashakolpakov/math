import OAI.AlgebraicGeometry.Crystalline.Cohomology.PadicPDP
import Mathlib.Algebra.Algebra.Pi

/-! # Inverse Limit -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.InverseLimit.PDInverseLimit

noncomputable section

/-!
# Inverse limits of crystalline divided-power rings

Compatible systems of sections form an actual ring. The divided powers
are taken coordinatewise; the reduction maps agree, so their defining
ideal is exactly the kernel of the limit's reduction.
-/

open _root_.CategoryTheory Opposite

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (B : Type u) [CommRing B] [Algebra k B]
  (F : ℕᵒᵖ ⥤ Thickening.AffinePDThickening p k B)

local notation "W" => WittVector p k
local notation "S" => fun n : ℕ => F.obj (op n)

def transition (n m : ℕ) (h : n ≤ m) : S m ⟶ S n := F.map (homOfLE h).op

/-- The ring of compatible sections in the inverse system. -/
def subalgebra : Subalgebra W (∀ n : ℕ, (S n).ring) where
  carrier x := ∀ n m h, (transition p k B F n m h).hom (x m) = x n
  zero_mem' n m h := map_zero (transition p k B F n m h).hom
  one_mem' n m h := map_one (transition p k B F n m h).hom
  add_mem' hx hy n m h := by rw [Pi.add_apply, map_add, hx n m h, hy n m h]; rfl
  mul_mem' hx hy n m h := by rw [Pi.mul_apply, map_mul, hx n m h, hy n m h]; rfl
  algebraMap_mem' w n m h := (transition p k B F n m h).hom.commutes w

abbrev Ring := subalgebra p k B F

/-- Projection of compatible sections onto one crystalline thickening. -/
def eval (n : ℕ) : Ring p k B F →ₐ[W] (S n).ring where
  toFun x := x.val n
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

theorem eval_compatible (n m : ℕ) (h : n ≤ m) (x : Ring p k B F) :
    (transition p k B F n m h).hom (eval p k B F m x) = eval p k B F n x := x.property n m h

theorem ext {x y : Ring p k B F} (h : ∀ n, eval p k B F n x = eval p k B F n y) : x = y :=
  Subtype.ext (funext h)

/-- Reduction of the inverse limit, evaluated at its zeroth coordinate. -/
def reduction : Ring p k B F →+* B := (S 0).reduction.comp (eval p k B F 0).toRingHom

theorem reduction_eval (n : ℕ) (x : Ring p k B F) :
    (S n).reduction (eval p k B F n x) = PDInverseLimit.reduction p k B F x := by
  calc
    _ = (S 0).reduction ((transition p k B F 0 n (Nat.zero_le n)).hom
        (eval p k B F n x)) :=
      (DFunLike.congr_fun (transition p k B F 0 n (Nat.zero_le n)).reduction_comp _).symm
    _ = PDInverseLimit.reduction p k B F x := congrArg (S 0).reduction (eval_compatible p k B F 0 n _ x)

theorem eval_mem_kernel (n : ℕ) {x : Ring p k B F} (hx : x ∈ RingHom.ker (PDInverseLimit.reduction p k B F)) :
    eval p k B F n x ∈ RingHom.ker (S n).reduction := by
  change (S n).reduction (eval p k B F n x) = 0
  exact (reduction_eval p k B F n x).trans hx

open scoped Classical in
/-- Coordinatewise divided powers on the reduction kernel, zero elsewhere. -/
def dpow (a : ℕ) (x : Ring p k B F) : Ring p k B F :=
  if hx : x ∈ RingHom.ker (PDInverseLimit.reduction p k B F) then
    ⟨fun n => (S n).dividedPowers.dpow a (eval p k B F n x), by
      intro n m h
      change (transition p k B F n m h).hom ((S m).dividedPowers.dpow a (eval p k B F m x)) = _
      have hd := (transition p k B F n m h).dp_comp.map_dpow (n := a)
        (eval_mem_kernel p k B F m hx)
      exact hd.trans (congrArg ((S n).dividedPowers.dpow a) (eval_compatible p k B F n m h x))⟩
  else 0

theorem eval_dpow (a n : ℕ) {x : Ring p k B F} (hx : x ∈ RingHom.ker (PDInverseLimit.reduction p k B F)) :
    eval p k B F n (PDInverseLimit.dpow p k B F a x) = (S n).dividedPowers.dpow a (eval p k B F n x) := by
  simp only [PDInverseLimit.dpow, dite_eq_left hx]
  rfl

theorem dpow_mem {a : ℕ} (ha : a ≠ 0) {x : Ring p k B F}
    (hx : x ∈ RingHom.ker (PDInverseLimit.reduction p k B F)) :
    PDInverseLimit.dpow p k B F a x ∈ RingHom.ker (PDInverseLimit.reduction p k B F) := by
  change (S 0).reduction (eval p k B F 0 (PDInverseLimit.dpow p k B F a x)) = 0
  rw [eval_dpow p k B F a 0 hx]
  exact (S 0).dividedPowers.dpow_mem ha (eval_mem_kernel p k B F 0 hx)

/-- Divided powers on the inverse limit's reduction kernel. -/
def dividedPowers : DividedPowers (RingHom.ker (PDInverseLimit.reduction p k B F)) where
  dpow := PDInverseLimit.dpow p k B F
  dpow_null hx := by simp only [PDInverseLimit.dpow, dite_eq_right hx]
  dpow_zero hx := by
    apply PDInverseLimit.ext p k B F
    intro n
    rw [eval_dpow p k B F 0 n hx, map_one]
    exact (S n).dividedPowers.dpow_zero (eval_mem_kernel p k B F n hx)
  dpow_one hx := by
    apply PDInverseLimit.ext p k B F
    intro n
    rw [eval_dpow p k B F 1 n hx]
    exact (S n).dividedPowers.dpow_one (eval_mem_kernel p k B F n hx)
  dpow_mem hn hx := PDInverseLimit.dpow_mem p k B F hn hx
  dpow_add hx hy := by
    apply PDInverseLimit.ext p k B F
    intro n
    simp only [eval_dpow p k B F _ n ((RingHom.ker _).add_mem hx hy), map_add,
      map_sum, map_mul, eval_dpow p k B F _ n hx, eval_dpow p k B F _ n hy]
    exact (S n).dividedPowers.dpow_add (eval_mem_kernel p k B F n hx) (eval_mem_kernel p k B F n hy)
  dpow_mul {a x y} hy := by
    apply PDInverseLimit.ext p k B F
    intro n
    simp only [eval_dpow p k B F _ n ((RingHom.ker _).mul_mem_left x hy), map_mul,
      map_pow, eval_dpow p k B F _ n hy]
    exact (S n).dividedPowers.dpow_mul (eval_mem_kernel p k B F n hy)
  mul_dpow hx := by
    apply PDInverseLimit.ext p k B F
    intro n
    simp only [map_mul, map_natCast, eval_dpow p k B F _ n hx]
    exact (S n).dividedPowers.mul_dpow (eval_mem_kernel p k B F n hx)
  dpow_comp hn hx := by
    apply PDInverseLimit.ext p k B F
    intro n
    simp only [eval_dpow p k B F _ n (PDInverseLimit.dpow_mem p k B F hn hx), map_mul, map_natCast,
      eval_dpow p k B F _ n hx]
    exact (S n).dividedPowers.dpow_comp hn (eval_mem_kernel p k B F n hx)

theorem eval_isDPMorphism (n : ℕ) :
    DividedPowers.IsDPMorphism (PDInverseLimit.dividedPowers p k B F) (S n).dividedPowers
      (eval p k B F n).toRingHom where
  ideal_comp := Ideal.map_le_iff_le_comap.mpr (fun _ hx => eval_mem_kernel p k B F n hx)
  dpow_comp {a} _x hx := (eval_dpow p k B F a n hx).symm

theorem base_isDPMorphism :
    DividedPowers.IsDPMorphism (Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
      (PDInverseLimit.dividedPowers p k B F) (algebraMap W (Ring p k B F)) where
  ideal_comp := Ideal.map_le_iff_le_comap.mpr (by
    intro w hw
    change (S 0).reduction (algebraMap W (S 0).ring w) = 0
    exact (S 0).baseDP.ideal_comp (Ideal.mem_map_of_mem _ hw))
  dpow_comp {a} w hw := by
    have hx : algebraMap W (Ring p k B F) w ∈ RingHom.ker (PDInverseLimit.reduction p k B F) := by
      change (S 0).reduction (algebraMap W (S 0).ring w) = 0
      exact (S 0).baseDP.ideal_comp (Ideal.mem_map_of_mem _ hw)
    apply PDInverseLimit.ext p k B F
    intro n
    change eval p k B F n (PDInverseLimit.dpow p k B F a (algebraMap W (Ring p k B F) w)) = _
    rw [eval_dpow p k B F a n hx]
    exact (S n).baseDP.dpow_comp w hw

variable (E : Type u) [CommRing E] [Algebra (WittVector p k) E]
  (r : E →+* B) (hr : Function.Surjective r)
  (hbase : r.comp (algebraMap (WittVector p k) E) =
    (algebraMap k B).comp WittVector.constantCoeff)
  (δ : DividedPowers (RingHom.ker r))
  (hδ : DividedPowers.IsDPMorphism (Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) δ
    (algebraMap (WittVector p k) E))

local notation "T" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PadicPDP.PadicPDThickening.tower p k B E r hr hbase δ hδ

/-- The p-adic ring defined as compatible residues modulo positive powers of p. -/
abbrev PadicRing := Ring p k B T

/-- The canonical algebra map into the p-power inverse limit. -/
def of : E →ₐ[W] PadicRing p k B E r hr hbase δ hδ where
  toFun x := ⟨fun n => Ideal.Quotient.mk (PadicPDP.PadicPDThickening.ideal p E n) x, by
    intro n m h
    exact PadicPDP.PadicPDThickening.transition_mk p k B E r hr hbase δ hδ n m h x⟩
  map_zero' := PDInverseLimit.ext p k B T (fun n => map_zero (Ideal.Quotient.mk (PadicPDP.PadicPDThickening.ideal p E n)))
  map_one' := PDInverseLimit.ext p k B T (fun n => map_one (Ideal.Quotient.mk (PadicPDP.PadicPDThickening.ideal p E n)))
  map_add' x y := PDInverseLimit.ext p k B T (fun n => map_add (Ideal.Quotient.mk (PadicPDP.PadicPDThickening.ideal p E n)) x y)
  map_mul' x y := PDInverseLimit.ext p k B T (fun n => map_mul (Ideal.Quotient.mk (PadicPDP.PadicPDThickening.ideal p E n)) x y)
  commutes' w := PDInverseLimit.ext p k B T (fun n => (Ideal.Quotient.mkₐ W (PadicPDP.PadicPDThickening.ideal p E n)).commutes w)

@[simp] theorem eval_of (n : ℕ) (x : E) :
    eval p k B T n (of p k B E r hr hbase δ hδ x) =
      Ideal.Quotient.mk (PadicPDP.PadicPDThickening.ideal p E n) x := rfl

@[simp] theorem reduction_of (x : E) :
    PDInverseLimit.reduction p k B T (of p k B E r hr hbase δ hδ x) = r x := rfl

/-- The completed ring still surjects onto the original residual algebra. -/
theorem reduction_surjective : Function.Surjective (PDInverseLimit.reduction p k B T) := by
  intro b
  obtain ⟨x, rfl⟩ := hr b
  exact ⟨of p k B E r hr hbase δ hδ x, rfl⟩

theorem of_isDPMorphism :
    DividedPowers.IsDPMorphism δ (PDInverseLimit.dividedPowers p k B T)
      (of p k B E r hr hbase δ hδ).toRingHom where
  ideal_comp := Ideal.map_le_iff_le_comap.mpr (fun _ hx => hx)
  dpow_comp {a} x hx := by
    apply PDInverseLimit.ext p k B T
    intro n
    change eval p k B T n (PDInverseLimit.dpow p k B T a (of p k B E r hr hbase δ hδ x)) = _
    rw [eval_dpow p k B T a n (show of p k B E r hr hbase δ hδ x ∈
      RingHom.ker (PDInverseLimit.reduction p k B T) from hx)]
    exact (PadicPDP.PadicPDThickening.quotient_isDPMorphism p k B E r δ hδ n).dpow_comp x hx

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.InverseLimit.PDInverseLimit
