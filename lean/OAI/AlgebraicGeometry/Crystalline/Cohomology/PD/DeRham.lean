import OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo
import Mathlib.RingTheory.DividedPowers.DPMorphism
import Mathlib.LinearAlgebra.Finsupp.Pi

/-! # De Rham -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham

noncomputable section

/-!
# Cohomology: the divided-power de Rham complex

For a divided-power ideal, impose the differential relations
`d γₘ₊₁(x) = γₘ(x) dx` on the ordinary algebraic forms. The exterior
differential descends to this quotient and still squares to zero.
-/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
variable (I : Ideal A) (δ : DividedPowers I)

structure RelationIndex (n : ℕ) where
  v : Fin n → A
  i : Fin n
  x : I
  m : ℕ

def relation (n : ℕ) (r : RelationIndex A I n) : DeRhamPresentationTo.DeRhamPresentation.Form R A n :=
  DeRhamPresentationTo.DeRhamPresentation.symbol R A 1 (Function.update r.v r.i (δ.dpow (r.m + 1) r.x)) -
    DeRhamPresentationTo.DeRhamPresentation.symbol R A (δ.dpow r.m r.x) (Function.update r.v r.i r.x)

def relations (n : ℕ) : Submodule A (DeRhamPresentationTo.DeRhamPresentation.Form R A n) :=
  Submodule.span A (Set.range (relation R A I δ n))

/-- Differential forms compatible with the divided powers. -/
abbrev Form (n : ℕ) := DeRhamPresentationTo.DeRhamPresentation.Form R A n ⧸ relations R A I δ n

def symbol {n : ℕ} (a : A) (v : Fin n → A) : Form R A I δ n :=
  (relations R A I δ n).mkQ (DeRhamPresentationTo.DeRhamPresentation.symbol R A a v)

theorem symbol_smul_one {n : ℕ} (a : A) (v : Fin n → A) :
    symbol R A I δ a v = a • symbol R A I δ 1 v := by
  unfold symbol
  rw [DeRhamPresentationTo.DeRhamPresentation.symbol_smul_one, map_smul]

theorem symbol_alt {n : ℕ} (v : Fin n → A) (i j : Fin n)
    (hij : v i = v j) (hne : i ≠ j) : symbol R A I δ 1 v = 0 := by
  unfold symbol
  rw [DeRhamPresentationTo.DeRhamPresentation.symbol_alt R A v i j hij hne, map_zero]

theorem symbol_cons_one {n : ℕ} (v : Fin n → A) :
    symbol R A I δ 1 (Fin.cons 1 v) = 0 := by
  unfold symbol
  rw [DeRhamPresentationTo.DeRhamPresentation.symbol_cons_one, map_zero]

theorem symbol_cons_mul {n : ℕ} (a b : A) (v : Fin n → A) :
    symbol R A I δ 1 (Fin.cons (a * b) v) =
      a • symbol R A I δ 1 (Fin.cons b v) +
        b • symbol R A I δ 1 (Fin.cons a v) := by
  unfold symbol
  rw [DeRhamPresentationTo.DeRhamPresentation.symbol_cons_mul, map_add, map_smul, map_smul]

/-- The defining differential divided-power relation. -/
theorem symbol_update_dpow {n : ℕ} (v : Fin n → A) (i : Fin n) (x : I) (m : ℕ) :
    symbol R A I δ 1 (Function.update v i (δ.dpow (m + 1) x)) =
      δ.dpow m x • symbol R A I δ 1 (Function.update v i x) := by
  have h : (relations R A I δ n).mkQ (relation R A I δ n ⟨v, i, x, m⟩) = 0 :=
    Submodule.Quotient.mk_eq_zero _ |>.mpr (Submodule.subset_span (Set.mem_range_self _))
  change (relations R A I δ n).mkQ (_ - _) = 0 at h
  rw [map_sub, sub_eq_zero] at h
  change symbol R A I δ 1 (Function.update v i (δ.dpow (m + 1) x)) =
    symbol R A I δ (δ.dpow m x) (Function.update v i x) at h
  exact h.trans (symbol_smul_one R A I δ _ _)

theorem symbol_dpow_repeated {n : ℕ} (v : Fin n → A) (i : Fin n) (x : I) (m : ℕ) :
    symbol R A I δ 1 (Fin.cons (δ.dpow m x) (Function.update v i x)) = 0 := by
  cases m with
  | zero => rw [δ.dpow_zero x.property, symbol_cons_one]
  | succ m =>
    have h := symbol_update_dpow R A I δ (Fin.cons 0 (Function.update v i x)) 0 x m
    simp only [Fin.update_cons_zero] at h
    rw [h]
    have hz : symbol R A I δ 1 (Fin.cons (x : A) (Function.update v i x)) = 0 :=
      symbol_alt R A I δ _ 0 i.succ (by simp)
        (fun h => Nat.succ_ne_zero i.val (congrArg Fin.val h).symm)
    rw [hz, smul_zero]

/-- Differentiate an ordinary form and project to divided-power forms. -/
def projectedDifferential (n : ℕ) : DeRhamPresentationTo.DeRhamPresentation.Form R A n →ₗ[R] Form R A I δ (n + 1) :=
  ((relations R A I δ (n + 1)).mkQ.restrictScalars R).comp
    (DeRhamPresentationTo.DeRhamPresentation.differential R A n)

@[simp]
theorem projectedDifferential_symbol {n : ℕ} (a : A) (v : Fin n → A) :
    projectedDifferential R A I δ n (DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) =
      symbol R A I δ 1 (Fin.cons a v) := by
  exact congrArg (relations R A I δ (n + 1)).mkQ (DeRhamPresentationTo.DeRhamPresentation.differential_symbol R A a v)

/-- The differential kills scalar multiples of the divided-power relations. -/
theorem projectedDifferential_smul_relation {n : ℕ} (a : A) (r : RelationIndex A I n) :
    projectedDifferential R A I δ n (a • relation R A I δ n r) = 0 := by
  have hs (b : A) (v : Fin n → A) :
      a • DeRhamPresentationTo.DeRhamPresentation.symbol R A b v = DeRhamPresentationTo.DeRhamPresentation.symbol R A (a * b) v := by
    rw [DeRhamPresentationTo.DeRhamPresentation.symbol_smul_one R A b v, smul_smul,
      ← DeRhamPresentationTo.DeRhamPresentation.symbol_smul_one]
  simp only [relation, smul_sub, hs, mul_one, map_sub, projectedDifferential_symbol]
  rw [symbol_cons_mul, Fin.cons_update, symbol_update_dpow]
  rw [← Fin.cons_update, symbol_dpow_repeated, smul_zero, zero_add, sub_self]

theorem projectedDifferential_relations {n : ℕ} (ω : DeRhamPresentationTo.DeRhamPresentation.Form R A n)
    (hω : ω ∈ relations R A I δ n) : projectedDifferential R A I δ n ω = 0 := by
  suffices h : ∀ a : A, projectedDifferential R A I δ n (a • ω) = 0 by simpa using h 1
  induction hω using Submodule.span_induction with
  | mem ω hω =>
    obtain ⟨r, rfl⟩ := hω
    exact fun a => projectedDifferential_smul_relation R A I δ a r
  | zero => simp
  | add ω η hω hη ihω ihη => intro a; simp only [smul_add, map_add, ihω, ihη, zero_add]
  | smul b ω hω ih => intro a; simpa only [smul_smul] using ih (a * b)

/-- The divided-power exterior differential. -/
def differential (n : ℕ) : Form R A I δ n →ₗ[R] Form R A I δ (n + 1) :=
  ((relations R A I δ n).restrictScalars R).liftQ (projectedDifferential R A I δ n)
    (fun ω hω => projectedDifferential_relations R A I δ ω hω)

@[simp]
theorem differential_mk (n : ℕ) (ω : DeRhamPresentationTo.DeRhamPresentation.Form R A n) :
    differential R A I δ n ((relations R A I δ n).mkQ ω) =
      (relations R A I δ (n + 1)).mkQ (DeRhamPresentationTo.DeRhamPresentation.differential R A n ω) := rfl

/-- The differential in the divided-power quotient squares to zero. -/
theorem differential_square (n : ℕ) (ω : Form R A I δ n) :
    differential R A I δ (n + 1) (differential R A I δ n ω) = 0 := by
  obtain ⟨ω, rfl⟩ := Submodule.mkQ_surjective (relations R A I δ n) ω
  rw [differential_mk, differential_mk, DeRhamPresentationTo.DeRhamPresentation.differential_square, map_zero]

/-- The divided-power de Rham complex of the algebra. -/
def complex : CochainComplex (ModuleCat.{u} R) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of R (Form R A I δ n))
    (fun n => ModuleCat.ofHom (differential R A I δ n))
    (fun n => ModuleCat.hom_ext (LinearMap.ext (differential_square R A I δ n)))

/-- The canonical quotient map from ordinary algebraic forms to forms
compatible with the divided powers, in every degree. -/
def quotientComplex : DeRhamPresentationTo.DeRhamPresentation.complex R A ⟶ complex R A I δ where
  f n := ModuleCat.ofHom ((relations R A I δ n).mkQ.restrictScalars R)
  comm' n m hnm := by
    change n + 1 = m at hnm
    subst m
    dsimp only [complex, DeRhamPresentationTo.DeRhamPresentation.complex]
    rw [CochainComplex.of_d, CochainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro ω
    change differential R A I δ n ((relations R A I δ n).mkQ ω) =
      (relations R A I δ (n + 1)).mkQ (DeRhamPresentationTo.DeRhamPresentation.differential R A n ω)
    exact differential_mk R A I δ n ω

theorem ordinary_relations_zero : DeRhamPresentationTo.DeRhamPresentation.relations R A 0 = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro _ ⟨r, rfl⟩
  cases r with
  | add v i x y => exact i.elim0
  | mul v i x y => exact i.elim0
  | base v i r => exact i.elim0
  | alt v i j hij hne => exact i.elim0

theorem relations_zero : relations R A I δ 0 = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro _ ⟨r, rfl⟩
  exact r.i.elim0

/-- Divided-power zero-forms are the ambient ring itself. -/
def degreeZeroEquiv : Form R A I δ 0 ≃ₗ[A] A :=
  (relations R A I δ 0).quotEquivOfEqBot (relations_zero R A I δ) ≪≫ₗ
    (DeRhamPresentationTo.DeRhamPresentation.relations R A 0).quotEquivOfEqBot (ordinary_relations_zero R A) ≪≫ₗ
    Finsupp.uniqueLinearEquiv A A (fun i : Fin 0 => i.elim0)

@[simp]
theorem degreeZeroEquiv_symbol (a : A) (v : Fin 0 → A) :
    degreeZeroEquiv R A I δ (symbol R A I δ a v) = a := by
  have hv : v = (fun i : Fin 0 => i.elim0) := Subsingleton.elim _ _
  subst v
  simp [degreeZeroEquiv, symbol, DeRhamPresentationTo.DeRhamPresentation.symbol]

theorem symbol_degreeZeroEquiv (ω : Form R A I δ 0) :
    symbol R A I δ (degreeZeroEquiv R A I δ ω) (fun i : Fin 0 => i.elim0) = ω := by
  apply (degreeZeroEquiv R A I δ).injective
  rw [degreeZeroEquiv_symbol]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham
