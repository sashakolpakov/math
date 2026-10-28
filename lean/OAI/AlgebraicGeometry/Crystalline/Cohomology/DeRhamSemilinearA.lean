import OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId
import OAI.NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap

/-! # De Rham Semilinear A -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamSemilinearA.DeRhamSemilinearMap

noncomputable section

/-!
# Simultaneous semilinear change of base and polynomial coefficients

The actual differential-symbol presentation is functorial when the
base-ring map is also allowed to change. This construction keeps the
specified scalar maps explicit and proves compatibility with the
original exterior differential.
-/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation

universe u

variable (R S A B : Type u) [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra S B] (σ : R →+* S) (f : A →+* B)
  (h : ∀ r, f (algebraMap R A r) = algebraMap S B (σ r))

def rawMap (n : ℕ) : DeRhamPresentationTo.DeRhamPresentation.Raw A n →ₛₗ[f] DeRhamPresentationTo.DeRhamPresentation.Raw B n :=
  (Finsupp.lmapDomain B B (fun v : Fin n → A => f ∘ v)).comp
    (Finsupp.mapRange.linearMap f.toSemilinearMap)

theorem rawMap_single (n : ℕ) (a : A) (v : Fin n → A) :
    rawMap A B f n (Finsupp.single v a) = Finsupp.single (f ∘ v) (f a) := by
  change Finsupp.mapDomain (fun v : Fin n → A => f ∘ v)
    (Finsupp.mapRange f f.map_zero (Finsupp.single v a)) = _
  rw [Finsupp.mapRange_single, Finsupp.mapDomain_single]

def relationMap {n : ℕ} : DeRhamPresentationTo.DeRhamPresentation.RelationIndex R A n → DeRhamPresentationTo.DeRhamPresentation.RelationIndex S B n
  | .add v i a b => .add (f ∘ v) i (f a) (f b)
  | .mul v i a b => .mul (f ∘ v) i (f a) (f b)
  | .base v i r => .base (f ∘ v) i (σ r)
  | .alt v i j hij hne => .alt (f ∘ v) i j (congrArg f hij) hne

theorem comp_update {n : ℕ} (v : Fin n → A) (i : Fin n) (a : A) :
    f ∘ Function.update v i a = Function.update (f ∘ v) i (f a) := by
  funext j
  by_cases hj : j = i <;> simp [hj]

include h in
theorem rawMap_relation {n : ℕ} (r : DeRhamPresentationTo.DeRhamPresentation.RelationIndex R A n) :
    rawMap A B f n (DeRhamPresentationTo.DeRhamPresentation.relation R A n r) = DeRhamPresentationTo.DeRhamPresentation.relation S B n (relationMap R S A B σ f r) := by
  cases r <;> simp only [DeRhamPresentationTo.DeRhamPresentation.relation, relationMap, map_sub, rawMap_single, map_one,
    map_add, map_mul, comp_update, h]

include h in
theorem rawMap_mem {n : ℕ} (v : DeRhamPresentationTo.DeRhamPresentation.Raw A n) (hv : v ∈ DeRhamPresentationTo.DeRhamPresentation.relations R A n) :
    rawMap A B f n v ∈ DeRhamPresentationTo.DeRhamPresentation.relations S B n := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨r, rfl⟩ := hv
    rw [rawMap_relation R S A B σ f h]
    exact Submodule.subset_span (Set.mem_range_self _)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add v w hv hw ihv ihw => rw [map_add]; exact Submodule.add_mem _ ihv ihw
  | smul a v hv ih => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ ih

def formMapA (n : ℕ) : DeRhamPresentationTo.DeRhamPresentation.Form R A n →ₛₗ[f] DeRhamPresentationTo.DeRhamPresentation.Form S B n :=
  (DeRhamPresentationTo.DeRhamPresentation.relations R A n).mapQ (DeRhamPresentationTo.DeRhamPresentation.relations S B n) (rawMap A B f n)
    (fun v hv => rawMap_mem R S A B σ f h v hv)

def formMap (n : ℕ) : DeRhamPresentationTo.DeRhamPresentation.Form R A n →ₛₗ[σ] DeRhamPresentationTo.DeRhamPresentation.Form S B n where
  __ := (formMapA R S A B σ f h n).toAddMonoidHom
  map_smul' r ω := by
    change formMapA R S A B σ f h n (r • ω) = σ r • formMapA R S A B σ f h n ω
    rw [← algebraMap_smul A r ω, map_smulₛₗ, h, algebraMap_smul]

theorem formMap_symbol (n : ℕ) (a : A) (v : Fin n → A) :
    formMap R S A B σ f h n (DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) = DeRhamPresentationTo.DeRhamPresentation.symbol S B (f a) (f ∘ v) := by
  change (DeRhamPresentationTo.DeRhamPresentation.relations S B n).mkQ (rawMap A B f n (Finsupp.single v a)) = _
  rw [rawMap_single]
  rfl

theorem formMap_differential (n : ℕ) (ω : DeRhamPresentationTo.DeRhamPresentation.Form R A n) :
    formMap R S A B σ f h (n + 1) (DeRhamPresentationTo.DeRhamPresentation.differential R A n ω) =
      DeRhamPresentationTo.DeRhamPresentation.differential S B n (formMap R S A B σ f h n ω) := by
  obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective (DeRhamPresentationTo.DeRhamPresentation.relations R A n) ω
  induction v using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add v w hv hw => simp only [map_add, hv, hw]
  | single v a =>
    change formMap R S A B σ f h (n + 1) (DeRhamPresentationTo.DeRhamPresentation.differential R A n (DeRhamPresentationTo.DeRhamPresentation.symbol R A a v)) =
      DeRhamPresentationTo.DeRhamPresentation.differential S B n (formMap R S A B σ f h n (DeRhamPresentationTo.DeRhamPresentation.symbol R A a v))
    rw [DeRhamPresentationTo.DeRhamPresentation.differential_symbol, formMap_symbol, formMap_symbol, DeRhamPresentationTo.DeRhamPresentation.differential_symbol, map_one]
    congr 1
    funext i
    exact Fin.cases rfl (fun _ => rfl) i

def complexMap : NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap.Map σ (DeRhamPresentationTo.DeRhamPresentation.complex R A) (DeRhamPresentationTo.DeRhamPresentation.complex S B) :=
  NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap.ofSuccessors
    (fun n => formMap R S A B σ f h n) (by
      intro n ω
      dsimp only [DeRhamPresentationTo.DeRhamPresentation.complex]
      rw [CochainComplex.of_d, CochainComplex.of_d]
      exact formMap_differential R S A B σ f h n ω)

theorem addHom_ext (n : ℕ) {M : Type*} [AddCommMonoid M]
    (g j : DeRhamPresentationTo.DeRhamPresentation.Form R A n →+ M) (hs : ∀ a v, g (DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) = j (DeRhamPresentationTo.DeRhamPresentation.symbol R A a v)) : g = j := by
  apply AddMonoidHom.ext
  intro ω
  obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective (DeRhamPresentationTo.DeRhamPresentation.relations R A n) ω
  induction v using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add v w hv hw => simp only [map_add, hv, hw]
  | single v a => exact hs a v

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamSemilinearA.DeRhamSemilinearMap
