import OAI.AlgebraicGeometry.DivisorClass.Chern.Compact.IntegralScaling
import OAI.AlgebraicGeometry.DivisorClass.Chern.LogRefinementOpen

/-! # Integral Refinement -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.IntegralRefinement

noncomputable section

section

/-! Finite shrinking refinements give compact control of every Čech overlap. -/

open _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {T I : Type} [TopologicalSpace T]

structure CompactCechRefinement (U : I → Opens T) where
  charts : Finset I
  cover : charts → Opens T
  closure_subset : ∀ i, closure (cover i : Set T) ⊆ U i.val
  covers : ∀ x : T, ∃ i, x ∈ cover i

theorem nonempty_compactCechRefinement [CompactSpace T] [NormalSpace T]
    (U : I → Opens T) (hU : ∀ x : T, ∃ i, x ∈ U i) : Nonempty (CompactCechRefinement U) := by
  classical
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun i => (U i : Set T)) (fun i => (U i).isOpen) (by
      intro x _
      exact Set.mem_iUnion.mpr (hU x))
  have hsc : ∀ x : T, ∃ i : s, x ∈ U i.val := by
    intro x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hs (Set.mem_univ x))
    obtain ⟨his, hxi⟩ := Set.mem_iUnion.mp hi
    exact ⟨⟨i, his⟩, hxi⟩
  obtain ⟨V, hVc, hVo, hVU⟩ := exists_subset_iUnion_closure_subset
    (s := (Set.univ : Set T)) isClosed_univ (fun i : s => (U i.val).isOpen)
    (fun x _ => Set.toFinite {i : s | x ∈ U i.val}) (by
      intro x _
      exact Set.mem_iUnion.mpr (hsc x))
  refine ⟨⟨s, fun i => ⟨V i, hVo i⟩, hVU, ?_⟩⟩
  intro x
  exact Set.mem_iUnion.mp (hVc (Set.mem_univ x))

def compactCechRefinement [CompactSpace T] [NormalSpace T]
    (U : I → Opens T) (hU : ∀ x : T, ∃ i, x ∈ U i) : CompactCechRefinement U :=
  Classical.choice (nonempty_compactCechRefinement U hU)

variable {U : I → Opens T} (r : CompactCechRefinement U)

theorem CompactCechRefinement.subset (i : r.charts) : r.cover i ≤ U i.val :=
  fun _ hx => r.closure_subset i (subset_closure hx)

theorem CompactCechRefinement.intersectionClosure_subset {n : ℕ} (a : Fin (n + 1) → r.charts) :
    closure (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection r.cover a : Set T) ⊆ AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U (Subtype.val ∘ a) := by
  intro x hx
  apply (AlgebraicTopology.DeRham.Comparison.SmoothCech.mem_cechIntersection U (Subtype.val ∘ a) x).mpr
  intro j
  exact r.closure_subset (a j) (closure_mono (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le r.cover a j) hx)

theorem CompactCechRefinement.intersectionClosure_isCompact [CompactSpace T]
    {n : ℕ} (a : Fin (n + 1) → r.charts) :
    IsCompact (closure (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection r.cover a : Set T)) :=
  isClosed_closure.isCompact

/-- Each original rational section has a common denominator on the whole refined overlap closure. -/
theorem CompactCechRefinement.intersection_clear_denominators [CompactSpace T]
    {n : ℕ} (a : Fin (n + 1) → r.charts)
    (f : LocallyConstant (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U (Subtype.val ∘ a)) ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∃ g : LocallyConstant (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection r.cover a) ℤ,
      ∀ x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection r.cover a, (g x : ℚ) =
        (N : ℚ) * f ⟨x.val, r.intersectionClosure_subset a (subset_closure x.property)⟩ := by
  obtain ⟨N, hN, g, hg⟩ := Compact.IntegralScaling.locallyConstant_rat_clear_denominators_on_compact
    (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U (Subtype.val ∘ a)) f
    (closure (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection r.cover a : Set T)) (r.intersectionClosure_isCompact a)
    (r.intersectionClosure_subset a)
  let g' : LocallyConstant (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection r.cover a) ℤ :=
    ⟨fun x => g ⟨x.val, subset_closure x.property⟩,
      g.isLocallyConstant.comp_continuous (continuous_subtype_val.subtype_mk _)⟩
  exact ⟨N, hN, g', fun x => hg ⟨x.val, subset_closure x.property⟩⟩

end

section

/-! One denominator simultaneously clears all actual overlaps of a finite Čech cochain. -/

open _root_.TopologicalSpace
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem finiteFamily_locallyConstant_integer_scale {I : Type} [Fintype I]
    {T : I → Type} [∀ i, TopologicalSpace (T i)] (f : ∀ i, LocallyConstant (T i) ℚ)
    (h : ∀ i, ∃ N : ℕ, 0 < N ∧ ∃ g : LocallyConstant (T i) ℤ,
      ∀ x, (g x : ℚ) = (N : ℚ) * f i x) :
    ∃ N : ℕ, 0 < N ∧ ∃ g : ∀ i, LocallyConstant (T i) ℤ,
      ∀ i x, (g i x : ℚ) = (N : ℚ) * f i x := by
  classical
  choose d hd g hg using h
  let N := ∏ i, d i
  have hN : 0 < N := Finset.prod_pos (fun i _ => hd i)
  have hdi (i : I) : d i ∣ N := Finset.dvd_prod_of_mem d (Finset.mem_univ i)
  refine ⟨N, hN, fun i => LocallyConstant.map (fun z : ℤ => ((N / d i : ℕ) : ℤ) * z) (g i), ?_⟩
  intro i x
  change ((((N / d i : ℕ) : ℤ) * g i x : ℤ) : ℚ) = (N : ℚ) * f i x
  have he : ((N / d i : ℕ) : ℚ) * d i = (N : ℚ) := by
    exact_mod_cast Nat.div_mul_cancel (hdi i)
  simp only [Int.cast_mul, Int.cast_natCast]
  rw [hg i x, ← mul_assoc, he]

variable {T I : Type} [TopologicalSpace T]
variable {U : I → Opens T} (r : CompactCechRefinement U)

theorem CompactCechRefinement.cochain_clear_denominators [CompactSpace T]
    (n : ℕ)
    (c : Rational.Cech.RationalCech.CechCochain (Obj.RationalCech.locallyConstantPresheaf (TopCat.of T)) U n) :
    ∃ N : ℕ, 0 < N ∧
      ∃ g : ∀ a : Fin (n + 1) → r.charts, LocallyConstant (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection r.cover a) ℤ,
        ∀ a (x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection r.cover a), (g a x : ℚ) =
          (N : ℚ) * c (Subtype.val ∘ a)
            ⟨x.val, r.intersectionClosure_subset a (subset_closure x.property)⟩ := by
  classical
  let f (a : Fin (n + 1) → r.charts) : LocallyConstant (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection r.cover a) ℚ :=
    ⟨fun x => c (Subtype.val ∘ a)
      ⟨x.val, r.intersectionClosure_subset a (subset_closure x.property)⟩,
      (c (Subtype.val ∘ a)).isLocallyConstant.comp_continuous (continuous_subtype_val.subtype_mk _)⟩
  exact finiteFamily_locallyConstant_integer_scale f
    (fun a => r.intersection_clear_denominators a (c (Subtype.val ∘ a)))

end

section

/-! Integer Čech cochains with the original alternating open-restriction differential. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {T I : Type} [TopologicalSpace T] (U : I → Opens T)

abbrev IntegerCechCochain (n : ℕ) :=
  ∀ a : Fin (n + 1) → I, LocallyConstant (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) ℤ

def integerCechRationalize (n : ℕ) : IntegerCechCochain U n →+
    Rational.Cech.RationalCech.CechCochain (Obj.RationalCech.locallyConstantPresheaf (TopCat.of T)) U n where
  toFun c a := LocallyConstant.mapAddMonoidHom (Int.castAddHom ℚ) (c a)
  map_zero' := by
    funext a
    exact map_zero (LocallyConstant.mapAddMonoidHom (Int.castAddHom ℚ))
  map_add' c d := by
    funext a
    exact map_add (LocallyConstant.mapAddMonoidHom (Int.castAddHom ℚ)) (c a) (d a)

theorem integerCechRationalize_injective (n : ℕ) : Function.Injective (integerCechRationalize U n) := by
  intro c d h
  funext a
  apply LocallyConstant.ext
  intro x
  exact Rat.intCast_injective (congrArg (fun f => (f a : LocallyConstant (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) ℚ) x) h)

def integerCechDelta (n : ℕ) (c : IntegerCechCochain U n) : IntegerCechCochain U (n + 1) :=
  fun a => ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val •
    ((IntegralConstantSheaf.locallyConstantIntegerPresheaf (TopCat.of T)).map
      (homOfLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a j.succAbove)).op (c (a ∘ j.succAbove)))

theorem integerCechRationalize_delta (n : ℕ) (c : IntegerCechCochain U n) :
    integerCechRationalize U (n + 1) (integerCechDelta U n c) =
      Rational.Cech.RationalCech.cechDelta (Obj.RationalCech.locallyConstantPresheaf (TopCat.of T)) U n
        (integerCechRationalize U n c) := by
  funext a
  change LocallyConstant.mapAddMonoidHom (Int.castAddHom ℚ)
    (∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val •
      ((IntegralConstantSheaf.locallyConstantIntegerPresheaf (TopCat.of T)).map
        (homOfLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a j.succAbove)).op (c (a ∘ j.succAbove)))) = _
  rw [map_sum, Rational.Cech.RationalCech.cechDelta_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_zsmul]
  congr 1

theorem integerCechDelta_squared (n : ℕ) (c : IntegerCechCochain U n) :
    integerCechDelta U (n + 1) (integerCechDelta U n c) = 0 := by
  apply integerCechRationalize_injective U (n + 2)
  rw [integerCechRationalize_delta, integerCechRationalize_delta,
    Rational.Cech.RationalCech.cechDelta_squared, map_zero]

end

/-! Every rational Čech cocycle on a compact normal space becomes integral after scaling and refinement. -/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {T I : Type} [TopologicalSpace T] [CompactSpace T] [NormalSpace T]

/-- The positive multiplier and the integer cocycle are constructed from the original rational cocycle. -/
theorem exists_integral_cech_refinement (U : I → Opens T) (hU : ∀ x : T, ∃ i, x ∈ U i)
    (n : ℕ)
    (c : Rational.Cech.RationalCech.CechCochain (Obj.RationalCech.locallyConstantPresheaf (TopCat.of T)) U n)
    (hc : Rational.Cech.RationalCech.cechDelta (Obj.RationalCech.locallyConstantPresheaf (TopCat.of T)) U n c = 0) :
    ∃ r : CompactCechRefinement U, ∃ N : ℕ, 0 < N ∧ ∃ g : IntegerCechCochain r.cover n,
      integerCechDelta r.cover n g = 0 ∧
      integerCechRationalize r.cover n g = (N : ℚ) •
        Rational.Cech.RationalCech.cechRefinementMap (Obj.RationalCech.locallyConstantPresheaf (TopCat.of T))
          U r.cover Subtype.val r.subset n c := by
  let r := compactCechRefinement U hU
  obtain ⟨N, hN, g, hg⟩ := r.cochain_clear_denominators n c
  have he : integerCechRationalize r.cover n g = (N : ℚ) •
      Rational.Cech.RationalCech.cechRefinementMap (Obj.RationalCech.locallyConstantPresheaf (TopCat.of T))
        U r.cover Subtype.val r.subset n c := by
    funext a
    apply LocallyConstant.ext
    intro x
    exact hg a x
  refine ⟨r, N, hN, g, ?_, he⟩
  apply integerCechRationalize_injective r.cover (n + 1)
  rw [integerCechRationalize_delta, he, map_smul,
    ← Rational.Cech.RationalCech.cechRefinementMap_delta, hc, map_zero, smul_zero, map_zero]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.IntegralRefinement
