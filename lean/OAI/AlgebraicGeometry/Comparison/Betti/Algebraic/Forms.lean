import Mathlib

/-! # Forms -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.Forms

noncomputable section

/-!
# Algebraic differential forms by generators and relations

A generator `(a₀, …, aₙ)` denotes `a₀ da₁ ∧ … ∧ daₙ`. The relations
are complex multilinearity, the Leibniz rule, vanishing differentials of
constants, and alternation, together with their exterior derivatives.
The differential sends this generator to `(1, a₀, …, aₙ)`.

These are algebraic constructions on a complex algebra. No Betti spaces or
comparison assertion enter their definitions.
-/

open _root_.CategoryTheory

universe u

variable (A : Type u) [CommRing A] [Algebra ℂ A]

abbrev RawForm (n : ℕ) := (Fin (n + 1) → A) →₀ ℂ

def symbol {n : ℕ} (a : Fin (n + 1) → A) : RawForm A n :=
  Finsupp.single a 1

def rawDifferential (n : ℕ) : RawForm A n →ₗ[ℂ] RawForm A (n + 1) :=
  Finsupp.lmapDomain ℂ ℂ (fun a : Fin (n + 1) → A => Fin.cons (1 : A) a)

omit [Algebra ℂ A] in
@[simp]
theorem rawDifferential_symbol {n : ℕ} (a : Fin (n + 1) → A) :
    rawDifferential A n (symbol A a) = symbol A (Fin.cons 1 a) := by
  simp [rawDifferential, symbol]

/-- The defining algebraic relations, closed under exterior differentiation. -/
inductive FormRelation : (n : ℕ) → RawForm A n → Prop
  | add (n : ℕ) (a : Fin (n + 1) → A) (i : Fin (n + 1)) (x y : A) :
      FormRelation n
        (symbol A (Function.update a i (x + y)) -
          symbol A (Function.update a i x) - symbol A (Function.update a i y))
  | smul (n : ℕ) (a : Fin (n + 1) → A) (i : Fin (n + 1)) (c : ℂ) (x : A) :
      FormRelation n
        (symbol A (Function.update a i (c • x)) -
          c • symbol A (Function.update a i x))
  | leibniz (n : ℕ) (a : Fin (n + 1) → A) (i : Fin n) (x y : A) :
      FormRelation n
        (symbol A (Function.update a i.succ (x * y)) -
          symbol A (Function.update (Function.update a 0 (a 0 * x)) i.succ y) -
          symbol A (Function.update (Function.update a 0 (a 0 * y)) i.succ x))
  | constant (n : ℕ) (a : Fin (n + 1) → A) (i : Fin n) (c : ℂ) :
      FormRelation n (symbol A (Function.update a i.succ (algebraMap ℂ A c)))
  | alternating (n : ℕ) (a : Fin (n + 1) → A) (i j : Fin n)
      (hij : i ≠ j) (ha : a i.succ = a j.succ) :
      FormRelation n (symbol A a)
  | differential {n : ℕ} {r : RawForm A n} (hr : FormRelation n r) :
      FormRelation (n + 1) (rawDifferential A n r)

def relations (n : ℕ) : Submodule ℂ (RawForm A n) :=
  Submodule.span ℂ {r | Forms.FormRelation A n r}

abbrev Form (n : ℕ) := RawForm A n ⧸ relations A n

def formSymbol {n : ℕ} (a : Fin (n + 1) → A) : Form A n :=
  (relations A n).mkQ (symbol A a)

theorem formSymbol_add {n : ℕ} (a : Fin (n + 1) → A) (i : Fin (n + 1))
    (x y : A) :
    formSymbol A (Function.update a i (x + y)) =
      formSymbol A (Function.update a i x) + formSymbol A (Function.update a i y) := by
  have h := (Submodule.Quotient.mk_eq_zero (relations A n)).mpr
    (Submodule.subset_span (Forms.FormRelation.add n a i x y))
  change (relations A n).mkQ (_ - _ - _) = 0 at h
  rw [map_sub, map_sub, sub_sub, sub_eq_zero] at h
  exact h

theorem formSymbol_smul {n : ℕ} (a : Fin (n + 1) → A) (i : Fin (n + 1))
    (c : ℂ) (x : A) :
    formSymbol A (Function.update a i (c • x)) =
      c • formSymbol A (Function.update a i x) := by
  have h := (Submodule.Quotient.mk_eq_zero (relations A n)).mpr
    (Submodule.subset_span (Forms.FormRelation.smul n a i c x))
  change (relations A n).mkQ (_ - c • _) = 0 at h
  rw [map_sub, map_smul, sub_eq_zero] at h
  exact h

theorem differential_mem_relations (n : ℕ) {r : RawForm A n}
    (hr : r ∈ relations A n) :
    rawDifferential A n r ∈ relations A (n + 1) := by
  induction hr using Submodule.span_induction with
  | mem x hx =>
      exact Submodule.subset_span (Forms.FormRelation.differential hx)
  | zero => simp
  | add x y hx hy ihx ihy =>
      simpa only [map_add] using (relations A (n + 1)).add_mem ihx ihy
  | smul c x hx ih =>
      simpa only [map_smul] using (relations A (n + 1)).smul_mem c ih

def differential (n : ℕ) : Form A n →ₗ[ℂ] Form A (n + 1) :=
  Submodule.mapQ (relations A n) (relations A (n + 1)) (rawDifferential A n)
    (fun _ hr => differential_mem_relations A n hr)

@[simp]
theorem differential_symbol {n : ℕ} (a : Fin (n + 1) → A) :
    Forms.differential A n (formSymbol A a) = formSymbol A (Fin.cons 1 a) := by
  change (relations A (n + 1)).mkQ (rawDifferential A n (symbol A a)) = _
  rw [rawDifferential_symbol]
  rfl

theorem double_differential_symbol_mem {n : ℕ} (a : Fin (n + 1) → A) :
    symbol A (Fin.cons 1 (Fin.cons 1 a)) ∈ relations A (n + 2) := by
  let b : Fin (n + 3) → A := Fin.cons (1 : A) (Fin.cons (1 : A) a)
  have h := Forms.FormRelation.constant (A := A) (n + 2) b 0 1
  have heq : Function.update b (Fin.succ 0) (algebraMap ℂ A 1) = b := by
    rw [map_one]
    exact Function.update_eq_self _ _
  apply Submodule.subset_span
  change Forms.FormRelation A (n + 2) (symbol A b)
  rw [← heq]
  exact h

theorem differential_squared (n : ℕ) :
    (Forms.differential A (n + 1)).comp (Forms.differential A n) = 0 := by
  apply LinearMap.ext
  intro x
  obtain ⟨r, rfl⟩ := (relations A n).mkQ_surjective x
  induction r using Finsupp.induction_linear with
  | zero => simp
  | add x y ihx ihy => simpa only [map_add] using congrArg₂ (· + ·) ihx ihy
  | single a c =>
      have hc : Finsupp.single a c = c • symbol A a := by simp [symbol]
      rw [hc]
      simp only [map_smul]
      suffices h : Forms.differential A (n + 1) (Forms.differential A n (formSymbol A a)) = 0 by
        simpa [formSymbol, LinearMap.comp_apply] using congrArg (c • ·) h
      rw [differential_symbol, differential_symbol]
      exact (Submodule.Quotient.mk_eq_zero (relations A (n + 2))).mpr
        (double_differential_symbol_mem A a)

/-- The algebraic de Rham complex of a complex algebra in the displayed
generators-and-relations presentation. -/
def algebraicDeRhamComplex : CochainComplex (ModuleCat.{u} ℂ) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of ℂ (Form A n))
    (fun n => ModuleCat.ofHom (Forms.differential A n))
    (fun n => ModuleCat.hom_ext (differential_squared A n))

@[simp]
theorem algebraicDeRhamComplex_d (n : ℕ) :
    (algebraicDeRhamComplex A).d n (n + 1) = ModuleCat.ofHom (Forms.differential A n) :=
  CochainComplex.of_d (fun k => ModuleCat.of ℂ (Form A k))
    (fun k => ModuleCat.ofHom (Forms.differential A k)) n

section Pullback

variable {A} {B C : Type u} [CommRing B] [Algebra ℂ B]
  [CommRing C] [Algebra ℂ C]

def rawPullback (f : A →ₐ[ℂ] B) (n : ℕ) : RawForm A n →ₗ[ℂ] RawForm B n :=
  Finsupp.lmapDomain ℂ ℂ (fun a => f ∘ a)

@[simp]
theorem rawPullback_symbol (f : A →ₐ[ℂ] B) {n : ℕ} (a : Fin (n + 1) → A) :
    rawPullback f n (symbol A a) = symbol B (f ∘ a) := by
  simp [rawPullback, symbol]

theorem rawPullback_differential (f : A →ₐ[ℂ] B) (n : ℕ) :
    (rawPullback f (n + 1)).comp (rawDifferential A n) =
      (rawDifferential B n).comp (rawPullback f n) := by
  apply Finsupp.lhom_ext
  intro a c
  have heq : f ∘ Fin.cons (1 : A) a = Fin.cons (1 : B) (f ∘ a) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · rfl
  simp [rawPullback, rawDifferential, Finsupp.mapDomain_single, heq]

theorem rawPullback_relation (f : A →ₐ[ℂ] B) {n : ℕ} {r : RawForm A n}
    (hr : Forms.FormRelation A n r) : Forms.FormRelation B n (rawPullback f n r) := by
  induction hr with
  | add n a i x y =>
      simpa only [map_sub, rawPullback_symbol, Function.comp_update, map_add] using
        (Forms.FormRelation.add (A := B) n (f ∘ a) i (f x) (f y))
  | smul n a i c x =>
      simpa only [map_sub, map_smul, rawPullback_symbol, Function.comp_update] using
        (Forms.FormRelation.smul (A := B) n (f ∘ a) i c (f x))
  | leibniz n a i x y =>
      simpa only [map_sub, rawPullback_symbol, Function.comp_update, map_mul,
        Function.comp_apply] using
        (Forms.FormRelation.leibniz (A := B) n (f ∘ a) i (f x) (f y))
  | constant n a i c =>
      simpa only [rawPullback_symbol, Function.comp_update, AlgHom.commutes] using
        (Forms.FormRelation.constant (A := B) n (f ∘ a) i c)
  | alternating n a i j hij ha =>
      rw [rawPullback_symbol]
      exact Forms.FormRelation.alternating n (f ∘ a) i j hij (congrArg f ha)
  | @differential n r hr ih =>
      rw [← LinearMap.comp_apply, rawPullback_differential, LinearMap.comp_apply]
      exact Forms.FormRelation.differential ih

theorem rawPullback_mem_relations (f : A →ₐ[ℂ] B) (n : ℕ) {r : RawForm A n}
    (hr : r ∈ relations A n) : rawPullback f n r ∈ relations B n := by
  induction hr using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (rawPullback_relation f hx)
  | zero => simp
  | add x y hx hy ihx ihy =>
      simpa only [map_add] using (relations B n).add_mem ihx ihy
  | smul c x hx ih =>
      simpa only [map_smul] using (relations B n).smul_mem c ih

def pullback (f : A →ₐ[ℂ] B) (n : ℕ) : Form A n →ₗ[ℂ] Form B n :=
  Submodule.mapQ (relations A n) (relations B n) (rawPullback f n)
    (fun _ hr => rawPullback_mem_relations f n hr)

@[simp]
theorem pullback_symbol (f : A →ₐ[ℂ] B) {n : ℕ} (a : Fin (n + 1) → A) :
    pullback f n (formSymbol A a) = formSymbol B (f ∘ a) := by
  change (relations B n).mkQ (rawPullback f n (symbol A a)) = _
  rw [rawPullback_symbol]
  rfl

theorem pullback_differential (f : A →ₐ[ℂ] B) (n : ℕ) :
    (pullback f (n + 1)).comp (Forms.differential A n) =
      (Forms.differential B n).comp (pullback f n) := by
  apply LinearMap.ext
  intro x
  obtain ⟨r, rfl⟩ := (relations A n).mkQ_surjective x
  change (relations B (n + 1)).mkQ (rawPullback f (n + 1) (rawDifferential A n r)) =
    (relations B (n + 1)).mkQ (rawDifferential B n (rawPullback f n r))
  exact congrArg ((relations B (n + 1)).mkQ)
    (LinearMap.congr_fun (rawPullback_differential f n) r)

theorem pullback_id (n : ℕ) : pullback (AlgHom.id ℂ A) n = LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨r, rfl⟩ := (relations A n).mkQ_surjective x
  change (relations A n).mkQ (rawPullback (AlgHom.id ℂ A) n r) =
    (relations A n).mkQ r
  exact congrArg ((relations A n).mkQ) Finsupp.mapDomain_id

theorem pullback_comp (f : A →ₐ[ℂ] B) (g : B →ₐ[ℂ] C) (n : ℕ) :
    pullback (g.comp f) n = (pullback g n).comp (pullback f n) := by
  apply LinearMap.ext
  intro x
  obtain ⟨r, rfl⟩ := (relations A n).mkQ_surjective x
  change (relations C n).mkQ (rawPullback (g.comp f) n r) =
    (relations C n).mkQ (rawPullback g n (rawPullback f n r))
  apply congrArg ((relations C n).mkQ)
  exact LinearMap.congr_fun (Finsupp.lmapDomain_comp ℂ ℂ
    (fun a : Fin (n + 1) → A => f ∘ a) (fun a : Fin (n + 1) → B => g ∘ a)) r

def complexPullback (f : A →ₐ[ℂ] B) :
    algebraicDeRhamComplex A ⟶ algebraicDeRhamComplex B :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (pullback f n))
    (fun n => by
      rw [algebraicDeRhamComplex_d, algebraicDeRhamComplex_d]
      exact ModuleCat.hom_ext (pullback_differential f n).symm)

theorem complexPullback_id :
    complexPullback (AlgHom.id ℂ A) = 𝟙 (algebraicDeRhamComplex A) := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact ModuleCat.hom_ext (pullback_id n)

theorem complexPullback_comp (f : A →ₐ[ℂ] B) (g : B →ₐ[ℂ] C) :
    complexPullback (g.comp f) = complexPullback f ≫ complexPullback g := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact ModuleCat.hom_ext (pullback_comp f g n)

end Pullback

/-- Functoriality is induced by algebra homomorphisms on all coefficients
of the displayed differential-form symbols. -/
def algebraicDeRhamFunctor : CommAlgCat.{u} ℂ ⥤ CochainComplex (ModuleCat.{u} ℂ) ℕ where
  obj A := algebraicDeRhamComplex A
  map f := complexPullback f.hom
  map_id _A := complexPullback_id
  map_comp f g := complexPullback_comp f.hom g.hom

def rawZeroEvaluation : RawForm A 0 →ₗ[ℂ] A :=
  Finsupp.linearCombination ℂ (fun a => a 0)

@[simp]
theorem rawZeroEvaluation_symbol (a : Fin 1 → A) :
    rawZeroEvaluation A (symbol A a) = a 0 := by
  simp [rawZeroEvaluation, symbol]

theorem zeroRelation_evaluates_zero {r : RawForm A 0} (hr : Forms.FormRelation A 0 r) :
    rawZeroEvaluation A r = 0 := by
  cases hr with
  | add n a i x y =>
      have hi : i = 0 := Fin.eq_zero i
      simp [hi]
  | smul n a i c x =>
      have hi : i = 0 := Fin.eq_zero i
      simp [hi]
  | leibniz n a i x y => exact Fin.elim0 i
  | constant n a i c => exact Fin.elim0 i
  | alternating n a i j hij ha => exact Fin.elim0 i

def zeroEvaluation : Form A 0 →ₗ[ℂ] A :=
  (relations A 0).liftQ (rawZeroEvaluation A)
    (Submodule.span_le.mpr (fun _ hr => zeroRelation_evaluates_zero A hr))

omit [CommRing A] [Algebra ℂ A] in
theorem update_fin_one (a x : A) :
    Function.update (fun _ : Fin (0 + 1) => a) 0 x = fun _ => x := by
  funext i
  have hi : i = 0 := Fin.eq_zero i
  simp [hi]

def zeroSymbol : A →ₗ[ℂ] Form A 0 where
  toFun a := formSymbol A (fun _ => a)
  map_add' x y := by
    simpa only [update_fin_one] using formSymbol_add A (fun _ : Fin (0 + 1) => 0) 0 x y
  map_smul' c x := by
    simpa only [update_fin_one, RingHom.id_apply] using
      formSymbol_smul A (fun _ : Fin (0 + 1) => 0) 0 c x

@[simp]
theorem zeroEvaluation_zeroSymbol (a : A) : zeroEvaluation A (zeroSymbol A a) = a :=
  rawZeroEvaluation_symbol A (fun _ => a)

theorem zeroSymbol_zeroEvaluation (x : Form A 0) :
    zeroSymbol A (zeroEvaluation A x) = x := by
  obtain ⟨r, rfl⟩ := (relations A 0).mkQ_surjective x
  induction r using Finsupp.induction_linear with
  | zero => simp
  | add r s ihr ihs => simp only [map_add, ihr, ihs]
  | single a c =>
      have hc : Finsupp.single a c = c • symbol A a := by simp [symbol]
      rw [hc]
      simp only [map_smul]
      apply congrArg (c • ·)
      change zeroSymbol A (rawZeroEvaluation A (symbol A a)) = formSymbol A a
      rw [rawZeroEvaluation_symbol]
      change formSymbol A (fun _ => a 0) = formSymbol A a
      congr 1
      funext i
      exact congrArg a (Fin.eq_zero i).symm

/-- The degree-zero term is canonically the original algebra, not a
substitute cohomology space. -/
def zeroFormsEquiv : Form A 0 ≃ₗ[ℂ] A :=
  LinearEquiv.ofLinearMap (zeroEvaluation A) (zeroSymbol A)
    (LinearMap.ext (zeroEvaluation_zeroSymbol A))
    (LinearMap.ext (zeroSymbol_zeroEvaluation A))

end

end OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.Forms
