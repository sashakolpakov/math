import OAI.AlgebraicGeometry.Crystalline.Cohomology.EnvelopeThickeningP
import Mathlib.CategoryTheory.Category.Preorder

/-! # Padic PDP -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.PadicPDP.PadicPDThickening

noncomputable section

/-!
# Crystalline thickenings modulo powers of p

Compatibility with the Witt divided powers makes every positive power of
the ideal `(p)` a sub-DP ideal. Its quotients are affine crystalline
objects even when their defining ideal has no uniform nilpotence bound.
-/

open _root_.CategoryTheory Opposite

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (B : Type u) [CommRing B] [Algebra k B]
  (E : Type u) [CommRing E] [Algebra (WittVector p k) E]
  (r : E →+* B) (hr : Function.Surjective r)
  (hbase : r.comp (algebraMap (WittVector p k) E) =
    (algebraMap k B).comp WittVector.constantCoeff)
  (δ : DividedPowers (RingHom.ker r))
  (hδ : DividedPowers.IsDPMorphism (Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) δ
    (algebraMap (WittVector p k) E))

def ideal (n : ℕ) : Ideal E := (Ideal.span {(p : E)}) ^ (n + 1)

omit [Algebra k B] in
include hδ in
theorem ideal_isSubDPIdeal (n : ℕ) : DividedPowers.IsSubDPIdeal δ (ideal p E n) := by
  have h := DividedPowers.isSubDPIdeal_map_of_isSubDPIdeal hδ
    (PD.Truncation.PDTruncation.power_isSubDPIdeal (WittVector p k) (Ideal.span {(p : WittVector p k)})
      (Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) n)
  simpa only [Ideal.map_pow, Ideal.map_span, Set.image_singleton, map_natCast, ideal] using h

abbrev Ring (n : ℕ) := E ⧸ ideal p E n

def reduction (n : ℕ) : Ring p E n →+* B :=
  Ideal.Quotient.lift (ideal p E n) r (ideal_isSubDPIdeal p k B E r δ hδ n).1

omit [Algebra k B] in
@[simp] theorem reduction_mk (n : ℕ) (x : E) :
    PadicPDThickening.reduction p k B E r δ hδ n (Ideal.Quotient.mk (ideal p E n) x) = r x := rfl

omit [Algebra k B] in
theorem reduction_kernel (n : ℕ) :
    RingHom.ker (PadicPDThickening.reduction p k B E r δ hδ n) =
      (RingHom.ker r).map (Ideal.Quotient.mk (ideal p E n)) :=
  Ideal.ker_quotient_lift (I := ideal p E n) r _

omit [Algebra k B] in
include hδ in
theorem quotientKernel_isSubDPIdeal (n : ℕ) :
    DividedPowers.IsSubDPIdeal δ
      (RingHom.ker (Ideal.Quotient.mk (ideal p E n)) ⊓ RingHom.ker r) := by
  rw [Ideal.mk_ker, inf_of_le_left (ideal_isSubDPIdeal p k B E r δ hδ n).1]
  exact ideal_isSubDPIdeal p k B E r δ hδ n

def dividedPowers (n : ℕ) : DividedPowers (RingHom.ker (PadicPDThickening.reduction p k B E r δ hδ n)) :=
  DividedPowers.Quotient.OfSurjective.dividedPowers δ Ideal.Quotient.mk_surjective
    (reduction_kernel p k B E r δ hδ n) (quotientKernel_isSubDPIdeal p k B E r δ hδ n)

omit [Algebra k B] in
theorem quotient_isDPMorphism (n : ℕ) :
    DividedPowers.IsDPMorphism δ (PadicPDThickening.dividedPowers p k B E r δ hδ n)
      (Ideal.Quotient.mk (ideal p E n)) :=
  DividedPowers.Quotient.OfSurjective.isDPMorphism δ Ideal.Quotient.mk_surjective
    (reduction_kernel p k B E r δ hδ n) (quotientKernel_isSubDPIdeal p k B E r δ hδ n)

omit [Fact (Nat.Prime p)] in
theorem p_pow_eq_zero (n : ℕ) : (p : Ring p E n) ^ (n + 1) = 0 := by
  have h : Ideal.Quotient.mk (ideal p E n) ((p : E) ^ (n + 1)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton (p : E))) (n + 1))
  simpa only [map_pow, map_natCast] using h

/-- The genuine crystalline object obtained by reduction modulo `p^(n+1)`. -/
def thickening (n : ℕ) : PD.Thickening.AffinePDThickening p k B where
  ring := CommRingCat.of (Ring p E n)
  reduction := PadicPDThickening.reduction p k B E r δ hδ n
  reduction_surjective b := by
    obtain ⟨x, rfl⟩ := hr b
    exact ⟨Ideal.Quotient.mk (ideal p E n) x, rfl⟩
  reduction_base := by
    ext w
    exact DFunLike.congr_fun hbase w
  p_nilpotent := ⟨n + 1, p_pow_eq_zero p E n⟩
  dividedPowers := PadicPDThickening.dividedPowers p k B E r δ hδ n
  baseDP := (quotient_isDPMorphism p k B E r δ hδ n).comp _ hδ

variable (T : PD.Thickening.AffinePDThickening p k B) (g : E →ₐ[WittVector p k] T.ring)
  (hg : T.reduction.comp g.toRingHom = r)
  (hgδ : DividedPowers.IsDPMorphism δ T.dividedPowers g.toRingHom)

theorem ideal_le_kernel (n : ℕ) (hn : (p : T.ring) ^ (n + 1) = 0) :
    ideal p E n ≤ RingHom.ker g := by
  rw [ideal, Ideal.span_singleton_pow, Ideal.span_le]
  rintro x (rfl : x = (p : E) ^ (n + 1))
  change g ((p : E) ^ (n + 1)) = 0
  simpa only [map_pow, map_natCast] using hn

/-- Factor a map through a sufficiently large p-power quotient. -/
def lift (n : ℕ) (hn : (p : T.ring) ^ (n + 1) = 0) :
    Ring p E n →ₐ[WittVector p k] T.ring where
  __ := Ideal.Quotient.lift (ideal p E n) g.toRingHom (ideal_le_kernel p k B E T g n hn)
  commutes' w := g.commutes w

@[simp] theorem lift_mk (n : ℕ) (hn : (p : T.ring) ^ (n + 1) = 0) (x : E) :
    PadicPDThickening.lift p k B E T g n hn (Ideal.Quotient.mk (ideal p E n) x) = g x := rfl

include hg in
theorem lift_reduction (n : ℕ) (hn : (p : T.ring) ^ (n + 1) = 0) :
    T.reduction.comp (PadicPDThickening.lift p k B E T g n hn).toRingHom = PadicPDThickening.reduction p k B E r δ hδ n := by
  apply RingHom.ext
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact DFunLike.congr_fun hg x

include hgδ in
theorem lift_isDPMorphism (n : ℕ) (hn : (p : T.ring) ^ (n + 1) = 0) :
    DividedPowers.IsDPMorphism (PadicPDThickening.dividedPowers p k B E r δ hδ n) T.dividedPowers
      (PadicPDThickening.lift p k B E T g n hn).toRingHom := by
  apply DividedPowers.IsDPMorphism.of_comp
    δ (PadicPDThickening.dividedPowers p k B E r δ hδ n) T.dividedPowers
    (Ideal.Quotient.mk (ideal p E n)) (PadicPDThickening.lift p k B E T g n hn).toRingHom
    (reduction_kernel p k B E r δ hδ n) (quotient_isDPMorphism p k B E r δ hδ n)
  exact hgδ

/-- Factorization as a morphism in the actual affine crystalline category. -/
def morphism (n : ℕ) (hn : (p : T.ring) ^ (n + 1) = 0) :
    thickening p k B E r hr hbase δ hδ n ⟶ T where
  hom := PadicPDThickening.lift p k B E T g n hn
  reduction_comp := lift_reduction p k B E r δ hδ T g hg n hn
  dp_comp := lift_isDPMorphism p k B E r δ hδ T g hgδ n hn

include hg hgδ in
theorem exists_morphism : ∃ n : ℕ, Nonempty (thickening p k B E r hr hbase δ hδ n ⟶ T) := by
  obtain ⟨n, hn⟩ := T.p_nilpotent
  have hn' : (p : T.ring) ^ (n + 1) = 0 := by rw [pow_succ, hn, zero_mul]
  exact ⟨n, ⟨morphism p k B E r hr hbase δ hδ T g hg hgδ n hn'⟩⟩

def quotient (n : ℕ) : E →ₐ[WittVector p k] (thickening p k B E r hr hbase δ hδ n).ring :=
  Ideal.Quotient.mkₐ (WittVector p k) (ideal p E n)

/-- The transition from a larger p-power quotient to a smaller one. -/
def transition (n m : ℕ) (h : n ≤ m) :
    thickening p k B E r hr hbase δ hδ m ⟶ thickening p k B E r hr hbase δ hδ n :=
  morphism p k B E r hr hbase δ hδ (thickening p k B E r hr hbase δ hδ n)
    (quotient p k B E r hr hbase δ hδ n) (by ext x; rfl)
    (quotient_isDPMorphism p k B E r δ hδ n) m
    (pow_eq_zero_of_le (Nat.add_le_add_right h 1) (p_pow_eq_zero p E n))

@[simp] theorem transition_mk (n m : ℕ) (h : n ≤ m) (x : E) :
    (transition p k B E r hr hbase δ hδ n m h).hom
      (Ideal.Quotient.mk (ideal p E m) x) = Ideal.Quotient.mk (ideal p E n) x := rfl

theorem transition_refl (n : ℕ) :
    transition p k B E r hr hbase δ hδ n n le_rfl = 𝟙 _ := by
  apply PD.Thickening.AffinePDThickening.Hom.ext
  apply AlgHom.ext
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

theorem transition_comp (l n m : ℕ) (hln : l ≤ n) (hnm : n ≤ m) :
    transition p k B E r hr hbase δ hδ n m hnm ≫
      transition p k B E r hr hbase δ hδ l n hln =
        transition p k B E r hr hbase δ hδ l m (hln.trans hnm) := by
  apply PD.Thickening.AffinePDThickening.Hom.ext
  apply AlgHom.ext
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- The actual inverse system of affine crystalline thickenings. -/
def tower : ℕᵒᵖ ⥤ PD.Thickening.AffinePDThickening p k B where
  obj n := thickening p k B E r hr hbase δ hδ n.unop
  map f := transition p k B E r hr hbase δ hδ _ _ (leOfHom f.unop)
  map_id n := transition_refl p k B E r hr hbase δ hδ n.unop
  map_comp f g := (transition_comp p k B E r hr hbase δ hδ _ _ _
    (leOfHom g.unop) (leOfHom f.unop)).symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.PadicPDP.PadicPDThickening
