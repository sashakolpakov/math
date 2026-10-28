import OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId
import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.Forms

/-! # Adapter -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.Adapter.FormsAdapter

noncomputable section

/-! Direct comparison of the two algebraic differential-form presentations.
Coefficients and differential entries are retained exactly, in every degree. -/

open _root_.CategoryTheory

namespace D62
open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation
variable (A : Type) [CommRing A] [Algebra ℂ A]

def coefficient (n : ℕ) (v : Fin n → A) : A →ₗ[ℂ] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form ℂ A n :=
  ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations ℂ A n).mkQ.comp (Finsupp.lsingle v)).restrictScalars ℂ

@[simp] theorem coefficient_apply (n : ℕ) (v : Fin n → A) (a : A) :
    coefficient A n v a = AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol ℂ A a v := rfl

theorem symbol_add (n : ℕ) (v : Fin n → A) (a b : A) :
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol ℂ A (a + b) v = AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol ℂ A a v + AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol ℂ A b v :=
  (coefficient A n v).map_add a b

theorem symbol_smul (n : ℕ) (v : Fin n → A) (c : ℂ) (a : A) :
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol ℂ A (c • a) v = c • AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol ℂ A a v :=
  (coefficient A n v).map_smul c a

theorem mul_symbol {n : ℕ} (a b : A) (v : Fin n → A) :
    a • AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol ℂ A b v = AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol ℂ A (a * b) v := by
  rw [AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol_smul_one ℂ A b v, smul_smul, ← AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol_smul_one]

theorem slot_add {n : ℕ} (a : A) (v : Fin n → A) (i : Fin n) (x y : A) :
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol ℂ A a (Function.update v i (x + y)) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol ℂ A a (Function.update v i x) + AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol ℂ A a (Function.update v i y) := by
  simpa only [smul_add, ← AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol_smul_one] using
    congrArg (a • ·) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol_update_add ℂ A v i x y)

theorem slot_mul {n : ℕ} (a : A) (v : Fin n → A) (i : Fin n) (x y : A) :
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol ℂ A a (Function.update v i (x * y)) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol ℂ A (a * x) (Function.update v i y) +
        AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol ℂ A (a * y) (Function.update v i x) := by
  simpa only [smul_add, mul_symbol, mul_one] using
    congrArg (a • ·) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol_update_mul ℂ A v i x y)

theorem slot_constant {n : ℕ} (a : A) (v : Fin n → A) (i : Fin n) (c : ℂ) :
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol ℂ A a (Function.update v i (algebraMap ℂ A c)) = 0 := by
  rw [AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol_smul_one, AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol_update_base, smul_zero]

theorem slot_smul {n : ℕ} (a : A) (v : Fin n → A) (i : Fin n) (c : ℂ) (x : A) :
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol ℂ A a (Function.update v i (c • x)) =
      c • AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol ℂ A a (Function.update v i x) := by
  rw [AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol_smul_one ℂ A a (Function.update v i (c • x)),
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol_smul_one ℂ A a (Function.update v i x)]
  have h := (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbols ℂ A n).map_update_smul v i c x
  change AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol ℂ A 1 (Function.update v i (c • x)) =
    c • AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol ℂ A 1 (Function.update v i x) at h
  rw [h, smul_comm a c]

end D62

namespace D66
open OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.Forms
variable (A : Type) [CommRing A] [Algebra ℂ A]

def coefficient (n : ℕ) (v : Fin n → A) : A →ₗ[ℂ] AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.Form A n where
  toFun a := AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.formSymbol A (Fin.cons a v)
  map_add' a b := by
    simpa only [Fin.update_cons_zero] using
      AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.formSymbol_add A (Fin.cons 0 v) 0 a b
  map_smul' c a := by
    simpa only [Fin.update_cons_zero, RingHom.id_apply] using
      AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.formSymbol_smul A (Fin.cons 0 v) 0 c a

@[simp] theorem coefficient_apply (n : ℕ) (v : Fin n → A) (a : A) :
    coefficient A n v a = AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.formSymbol A (Fin.cons a v) := rfl

theorem symbol_leibniz {n : ℕ} (a : A) (v : Fin n → A) (i : Fin n) (x y : A) :
    AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.formSymbol A (Fin.cons a (Function.update v i (x * y))) =
      AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.formSymbol A (Fin.cons (a * x) (Function.update v i y)) +
        AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.formSymbol A (Fin.cons (a * y) (Function.update v i x)) := by
  have h := (Submodule.Quotient.mk_eq_zero (AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.relations A n)).mpr
    (Submodule.subset_span (AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.FormRelation.leibniz n (Fin.cons a v) i x y))
  change (AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.relations A n).mkQ (_ - _ - _) = 0 at h
  rw [map_sub, map_sub, sub_sub, sub_eq_zero] at h
  simpa only [AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.formSymbol, Fin.cons_zero, ← Fin.cons_update, Fin.update_cons_zero] using h

theorem symbol_constant {n : ℕ} (a : A) (v : Fin n → A) (i : Fin n) (c : ℂ) :
    AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.formSymbol A (Fin.cons a (Function.update v i (algebraMap ℂ A c))) = 0 := by
  have h := (Submodule.Quotient.mk_eq_zero (AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.relations A n)).mpr
    (Submodule.subset_span (AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.FormRelation.constant n (Fin.cons a v) i c))
  change (AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.relations A n).mkQ _ = 0 at h
  simpa only [AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.formSymbol, ← Fin.cons_update] using h

theorem symbol_alternating {n : ℕ} (a : A) (v : Fin n → A) (i j : Fin n)
    (hij : i ≠ j) (hv : v i = v j) : AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.formSymbol A (Fin.cons a v) = 0 :=
  (Submodule.Quotient.mk_eq_zero (AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.relations A n)).mpr
    (Submodule.subset_span (AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.FormRelation.alternating n (Fin.cons a v) i j hij hv))

end D66

variable (A : Type) [CommRing A] [Algebra ℂ A]

def to62Raw (n : ℕ) : AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.RawForm A n →ₗ[ℂ]
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form ℂ A n :=
  Finsupp.linearCombination ℂ (fun a =>
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol ℂ A (a 0) (Fin.tail a))

@[simp] theorem to62Raw_symbol {n : ℕ} (a : Fin (n + 1) → A) :
    to62Raw A n (AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.symbol A a) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol ℂ A (a 0) (Fin.tail a) := by
  simp [to62Raw, AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.symbol]

theorem to62Raw_differential (n : ℕ) (r : AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.RawForm A n) :
    to62Raw A (n + 1) (AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.rawDifferential A n r) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential ℂ A n (to62Raw A n r) := by
  induction r using Finsupp.induction_linear with
  | zero => simp
  | add r s hr hs => simp only [map_add, hr, hs]
  | single a c =>
    have hc : Finsupp.single a c = c • AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.symbol A a := by
      simp [AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.symbol]
    rw [hc]
    simp only [map_smul, AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.rawDifferential_symbol, to62Raw_symbol,
      Fin.cons_zero, Fin.tail_cons, AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential_symbol,
      Fin.cons_self_tail]

theorem to62Raw_relation {n : ℕ} {r : AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.RawForm A n}
    (hr : AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.FormRelation A n r) : to62Raw A n r = 0 := by
  induction hr with
  | add n a i x y =>
    rcases Fin.eq_zero_or_eq_succ i with hi | ⟨j, hi⟩
    · subst i
      simp only [map_sub, map_add, to62Raw_symbol, Function.update_self,
        Fin.tail_update_zero, D62.symbol_add, sub_sub, sub_self]
    · subst i
      simp only [map_sub, map_add, to62Raw_symbol, Function.update_of_ne (Ne.symm j.succ_ne_zero),
        Fin.tail_update_succ, D62.slot_add, sub_sub, sub_self]
  | smul n a i c x =>
    rcases Fin.eq_zero_or_eq_succ i with hi | ⟨j, hi⟩
    · subst i
      simp only [map_sub, map_smul, to62Raw_symbol, Function.update_self,
        Fin.tail_update_zero, D62.symbol_smul, sub_self]
    · subst i
      simp only [map_sub, map_smul, to62Raw_symbol,
        Function.update_of_ne (Ne.symm j.succ_ne_zero), Fin.tail_update_succ,
        D62.slot_smul, sub_self]
  | leibniz n a i x y =>
    simp only [map_sub, map_add, to62Raw_symbol,
      Function.update_of_ne (Ne.symm i.succ_ne_zero), Function.update_self,
      Fin.tail_update_succ, Fin.tail_update_zero,
      D62.slot_mul, sub_sub, sub_self]
  | constant n a i c =>
    simp only [to62Raw_symbol, Function.update_of_ne (Ne.symm i.succ_ne_zero),
      Fin.tail_update_succ, D62.slot_constant]
  | alternating n a i j hij hv =>
    rw [to62Raw_symbol, AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol_smul_one,
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol_alt ℂ A (Fin.tail a) i j hv hij, smul_zero]
  | differential hr ih => rw [to62Raw_differential, ih, map_zero]

def to62 (n : ℕ) : AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.Form A n →ₗ[ℂ]
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form ℂ A n :=
  (AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.relations A n).liftQ (to62Raw A n)
    (Submodule.span_le.mpr (fun _ hr => to62Raw_relation A hr))

@[simp] theorem to62_symbol {n : ℕ} (a : Fin (n + 1) → A) :
    to62 A n (AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.formSymbol A a) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol ℂ A (a 0) (Fin.tail a) :=
  to62Raw_symbol A a

def to66Raw (n : ℕ) : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Raw A n →ₗ[ℂ] AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.Form A n :=
  Finsupp.lsum ℂ (D66.coefficient A n)

@[simp] theorem to66Raw_single {n : ℕ} (v : Fin n → A) (a : A) :
    to66Raw A n (Finsupp.single v a) = AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.formSymbol A (Fin.cons a v) :=
  Finsupp.lsum_single _ _ _ _

theorem to66Raw_relation {n : ℕ}
    (r : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.RelationIndex ℂ A n) (a : A) :
    to66Raw A n (a • AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relation ℂ A n r) = 0 := by
  cases r with
  | add v i x y =>
    simp only [AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relation, smul_sub, Finsupp.smul_single,
      smul_eq_mul, mul_one, map_sub, to66Raw_single]
    have h := AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.formSymbol_add A (Fin.cons a v) i.succ x y
    simp only [← Fin.cons_update] at h
    rw [h, sub_sub, sub_self]
  | mul v i x y =>
    simp only [AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relation, smul_sub, smul_add,
      Finsupp.smul_single, smul_eq_mul, mul_one, map_sub, map_add,
      to66Raw_single, D66.symbol_leibniz, sub_sub, sub_self]
  | base v i c =>
    simp only [AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relation, Finsupp.smul_single,
      smul_eq_mul, mul_one, to66Raw_single, D66.symbol_constant]
  | alt v i j hv hij =>
    simp only [AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relation, Finsupp.smul_single,
      smul_eq_mul, mul_one, to66Raw_single, D66.symbol_alternating A a v i j hij hv]

theorem to66Raw_relations {n : ℕ} {r : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Raw A n}
    (hr : r ∈ AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations ℂ A n) : to66Raw A n r = 0 := by
  have h : ∀ a : A, to66Raw A n (a • r) = 0 := by
    induction hr using Submodule.span_induction with
    | mem r hr => obtain ⟨r, rfl⟩ := hr; exact to66Raw_relation A r
    | zero => intro a; simp
    | add r s hr hs ihr ihs => intro a; simp only [smul_add, map_add, ihr, ihs, add_zero]
    | smul b r hr ihr => intro a; simpa only [smul_smul] using ihr (a * b)
  simpa only [one_smul] using h 1

def to66 (n : ℕ) : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form ℂ A n →ₗ[ℂ] AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.Form A n :=
  ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations ℂ A n).restrictScalars ℂ).liftQ
    (to66Raw A n) (fun _ hr => to66Raw_relations A hr)

@[simp] theorem to66_symbol {n : ℕ} (a : A) (v : Fin n → A) :
    to66 A n (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol ℂ A a v) =
      AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.formSymbol A (Fin.cons a v) := to66Raw_single A v a

theorem to62_to66 (n : ℕ) (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form ℂ A n) :
    to62 A n (to66 A n x) = x := by
  obtain ⟨r, rfl⟩ := (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations ℂ A n).mkQ_surjective x
  induction r using Finsupp.induction_linear with
  | zero => simp
  | add r s hr hs => simp only [map_add, hr, hs]
  | single v a =>
    change to62 A n (to66 A n (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol ℂ A a v)) = _
    simp only [to66_symbol, to62_symbol, Fin.cons_zero, Fin.tail_cons]
    rfl

theorem to66_to62 (n : ℕ) (x : AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.Form A n) : to66 A n (to62 A n x) = x := by
  obtain ⟨r, rfl⟩ := (AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.relations A n).mkQ_surjective x
  induction r using Finsupp.induction_linear with
  | zero => simp
  | add r s hr hs => simp only [map_add, hr, hs]
  | single a c =>
    have hc : Finsupp.single a c = c • AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.symbol A a := by simp [AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.symbol]
    rw [hc]
    simp only [map_smul]
    apply congrArg (c • ·)
    change to66 A n (to62 A n (AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.formSymbol A a)) = AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.formSymbol A a
    rw [to62_symbol, to66_symbol, Fin.cons_self_tail]

/-- Canonical equivalence in every degree; neither comparison theorem is used. -/
def formsEquiv (n : ℕ) : AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.Form A n ≃ₗ[ℂ]
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form ℂ A n where
  __ := to62 A n
  invFun := to66 A n
  left_inv := to66_to62 A n
  right_inv := to62_to66 A n

theorem to62_differential (n : ℕ) (x : AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.Form A n) :
    to62 A (n + 1) (AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.differential A n x) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential ℂ A n (to62 A n x) := by
  obtain ⟨r, rfl⟩ := (AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.relations A n).mkQ_surjective x
  exact to62Raw_differential A n r

theorem to62_pullback {B : Type} [CommRing B] [Algebra ℂ B]
    (f : A →ₐ[ℂ] B) (n : ℕ) (x : AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.Form A n) :
    to62 B n (AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.pullback f n x) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap (CommAlgCat.ofHom f) n (to62 A n x) := by
  obtain ⟨r, rfl⟩ := (AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.relations A n).mkQ_surjective x
  induction r using Finsupp.induction_linear with
  | zero => simp
  | add r s hr hs => simp only [map_add, hr, hs]
  | single a c =>
    have hc : Finsupp.single a c = c • AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.symbol A a := by
      simp [AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.symbol]
    rw [hc]
    simp only [map_smul]
    apply congrArg (c • ·)
    change to62 B n (AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.pullback f n (AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.formSymbol A a)) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap (CommAlgCat.ofHom f) n
        (to62 A n (AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.formSymbol A a))
    rw [AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.pullback_symbol, to62_symbol, to62_symbol,
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_symbol]
    rfl

theorem to66_differential (n : ℕ)
    (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form ℂ A n) :
    to66 A (n + 1) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential ℂ A n x) =
      AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.differential A n (to66 A n x) := by
  apply (formsEquiv A (n + 1)).injective
  change to62 A (n + 1) _ = to62 A (n + 1) _
  rw [to62_to66, to62_differential, to62_to66]

theorem to66_pullback {B : Type} [CommRing B] [Algebra ℂ B]
    (f : A →ₐ[ℂ] B) (n : ℕ) (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form ℂ A n) :
    to66 B n (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap (CommAlgCat.ofHom f) n x) =
      AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.pullback f n (to66 A n x) := by
  apply (formsEquiv B n).injective
  change to62 B n _ = to62 B n _
  rw [to62_to66, to62_pullback, to62_to66]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.Adapter.FormsAdapter
