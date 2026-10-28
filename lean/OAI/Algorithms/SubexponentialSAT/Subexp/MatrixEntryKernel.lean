import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixSupport

namespace OAI.Algorithms

/-!
# Scalar kernels of the actual multicolor matrix

The tensor coordinates below describe entries of the existing swap/projector
operator. They do not introduce a new matrix chosen only for its rank or support.
-/

namespace SubexponentialSAT.Subexp.MatrixEntryKernel

open SubexponentialSAT.MulticolorTypes
open scoped BigOperators

variable {r Q Δ : ℕ}

def pair (i : Fin Δ) (u : UniversalType r Q Δ) (l : Fin Q) : Fin r × Fin r :=
  (u.head l, u.slot i l)

def SpectatorsAgree (i : Fin Δ) (u y : UniversalType r Q Δ) : Prop :=
  ∀ j, j ≠ i → ∀ l, u.slot j l = y.slot j l

instance spectatorsAgreeDecidable (i : Fin Δ) (u y : UniversalType r Q Δ) :
    Decidable (SpectatorsAgree i u y) := by
  unfold SpectatorsAgree
  infer_instance

theorem eq_iff_pair_spectators (i : Fin Δ) (u y : UniversalType r Q Δ) :
    u = y ↔ SpectatorsAgree i u y ∧ ∀ l, pair i u l = pair i y l := by
  constructor
  · rintro rfl
    exact ⟨fun _ _ _ => rfl, fun _ => rfl⟩
  · rintro ⟨hs, hp⟩
    apply UniversalType.ext
    · funext l
      exact congrArg Prod.fst (hp l)
    · funext j l
      by_cases hj : j = i
      · subst j
        exact congrArg Prod.snd (hp l)
      · exact hs j hj l

section Field

variable {K : Type*} [Field K]

noncomputable def background (i : Fin Δ) (u y : UniversalType r Q Δ) : K :=
  if SpectatorsAgree i u y then 1 else 0

def plain (i : Fin Δ) (u y : UniversalType r Q Δ) (l : Fin Q) : K :=
  if pair i u l = pair i y l then 1 else 0

def flipped (i : Fin Δ) (u y : UniversalType r Q Δ) (l : Fin Q) : K :=
  if (u.slot i l, u.head l) = pair i y l then 1 else 0

@[simp] theorem background_swap (i : Fin Δ) (s : Finset (Fin Q))
    (u y : UniversalType r Q Δ) :
    background (K := K) i (MatrixSupport.swapPositions i s u) y = background i u y := by
  classical
  have h : SpectatorsAgree i (MatrixSupport.swapPositions i s u) y ↔
      SpectatorsAgree i u y := by
    constructor
    · intro hs j hj l
      simpa only [MatrixSupport.swapPositions_slot_other i j hj] using hs j hj l
    · intro hs j hj l
      simpa only [MatrixSupport.swapPositions_slot_other i j hj] using hs j hj l
  simp only [background, h]

@[simp] theorem plain_swap (i : Fin Δ) (s : Finset (Fin Q))
    (u y : UniversalType r Q Δ) (l : Fin Q) :
    plain (K := K) i (MatrixSupport.swapPositions i s u) y l =
      if l ∈ s then flipped i u y l else plain i u y l := by
  by_cases h : l ∈ s <;> simp [plain, flipped, pair, h]

@[simp] theorem flipped_swap (i : Fin Δ) (s : Finset (Fin Q))
    (u y : UniversalType r Q Δ) (l : Fin Q) :
    flipped (K := K) i (MatrixSupport.swapPositions i s u) y l =
      if l ∈ s then plain i u y l else flipped i u y l := by
  by_cases h : l ∈ s <;> simp [plain, flipped, pair, h]

theorem delta_eq_product (i : Fin Δ) (u y : UniversalType r Q Δ) :
    MatrixSupport.delta y u =
      background (K := K) i u y * ∏ l, plain i u y l := by
  classical
  by_cases h : u = y
  · subst y
    simp [MatrixSupport.delta, background, SpectatorsAgree, plain]
  · by_cases hs : SpectatorsAgree i u y
    · have hp : ¬ ∀ l, pair i u l = pair i y l :=
        fun hp => h ((eq_iff_pair_spectators i u y).mpr ⟨hs, hp⟩)
      simp [MatrixSupport.delta, h, background, hs, plain, Fintype.prod_boole, hp]
    · simp [MatrixSupport.delta, h, background, hs]

def factor (i : Fin Δ) (s : Finset (Fin Q))
    (u y : UniversalType r Q Δ) (l : Fin Q) : K :=
  if l ∈ s then plain i u y l - flipped i u y l else plain i u y l

noncomputable def partialKernel (i : Fin Δ) (s : Finset (Fin Q))
    (u y : UniversalType r Q Δ) : K :=
  background i u y * ∏ l, factor i s u y l

theorem partialKernel_empty (i : Fin Δ) (u y : UniversalType r Q Δ) :
    partialKernel (K := K) i ∅ u y = MatrixSupport.delta y u := by
  simp only [partialKernel, factor, Finset.notMem_empty, ↓reduceIte]
  exact (delta_eq_product i u y).symm

theorem partialKernel_insert (i : Fin Δ) (s : Finset (Fin Q))
    (a : Fin Q) (ha : a ∉ s) (u y : UniversalType r Q Δ) :
    partialKernel (K := K) i (insert a s) u y =
      partialKernel i s u y -
        partialKernel i s (MatrixSupport.swapPositions i {a} u) y := by
  classical
  let rest := ∏ l ∈ (Finset.univ : Finset (Fin Q)).erase a, factor (K := K) i s u y l
  have hrest :
      (∏ l ∈ (Finset.univ : Finset (Fin Q)).erase a, factor (K := K) i (insert a s) u y l) =
        rest := by
    apply Finset.prod_congr rfl
    intro l hl
    have hla : l ≠ a := (Finset.mem_erase.mp hl).1
    simp [factor, hla]
  have hswap :
      (∏ l ∈ (Finset.univ : Finset (Fin Q)).erase a,
        factor (K := K) i s (MatrixSupport.swapPositions i {a} u) y l) = rest := by
    apply Finset.prod_congr rfl
    intro l hl
    have hla : l ≠ a := (Finset.mem_erase.mp hl).1
    simp [factor, hla]
  have hprod (f : Fin Q → K) :
      (∏ l, f l) = f a * ∏ l ∈ (Finset.univ : Finset (Fin Q)).erase a, f l :=
    (Finset.mul_prod_erase Finset.univ f (Finset.mem_univ a)).symm
  unfold partialKernel
  rw [background_swap, hprod, hprod, hprod, hrest, hswap]
  simp only [factor, Finset.mem_insert_self, ite_true, ha, ite_false,
    plain_swap, Finset.mem_singleton_self, ite_true]
  dsimp only [rest, factor]
  ring

/-- Each actual difference operator affects exactly its own coordinate pair. -/
theorem differenceProduct_eq_partialKernel (i : Fin Δ) (as : List (Fin Q))
    (ha : as.Nodup) (u y : UniversalType r Q Δ) :
    MatrixSupport.differenceProduct i as (MatrixSupport.delta y) u =
      partialKernel (K := K) i as.toFinset u y := by
  induction as generalizing u with
  | nil => exact (partialKernel_empty i u y).symm
  | cons a as ih =>
      have hn := List.nodup_cons.mp ha
      rw [MatrixSupport.differenceProduct, ih hn.2, ih hn.2, List.toFinset_cons]
      exact (partialKernel_insert i as.toFinset a (by simpa using hn.1) u y).symm

end Field

end SubexponentialSAT.Subexp.MatrixEntryKernel

end OAI.Algorithms
