import OAI.AlgebraicGeometry.ComplexMultiplication.KnownExteriorCohomology
import OAI.AlgebraicTopology.Products.CupGradedCommutativity
import OAI.AlgebraicTopology.DeRham.Comparison.ProjectiveDegreeBounds
import Mathlib.LinearAlgebra.Multilinear.Curry

/-! # Cup Map -/

namespace OAI.AlgebraicGeometry.AbelianVariety.CupMap.Constructions.ExteriorCohomology

/-!
# Canonical rational exterior cup maps

The maps are induced by actual iterated cup products, including the degree-zero
unit. This file proves their normalization and uniqueness, the degree-one
comparison, and an exact characterization of the full comparison data.
The unconditional all-degree theorem is proved in `Proofs/ExteriorCohomology.lean`.
-/

open _root_.CategoryTheory
open scoped TensorProduct

open OAI.AlgebraicGeometry.ComplexMultiplication.KnownExteriorCohomology.CM

/-- Rational degree-one classes have zero cup square. -/
theorem h1_cup_self (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (x : A.variety.rationalCohomology 1) :
    AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (Betti.Scheme.schemePointSpace A.toOver) 1 1 x x = 0 := by
  have h := AlgebraicTopology.Products.CupGradedCommutativity.singularCohomologyCup_graded_comm
    (Betti.Scheme.schemePointSpace A.toOver) x x
  have hneg : AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (Betti.Scheme.schemePointSpace A.toOver) 1 1 x x =
      - AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (Betti.Scheme.schemePointSpace A.toOver) 1 1 x x := by
    simpa [AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCast] using h
  have hadd : (2 : ℚ) •
      AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (Betti.Scheme.schemePointSpace A.toOver) 1 1 x x = 0 := by
    simpa only [two_smul] using (eq_neg_iff_add_eq_zero.mp hneg)
  exact (smul_eq_zero.mp hadd).resolve_left (by norm_num)

/-- Iterated actual cup products, as multilinear maps including degree zero. -/
noncomputable def h1CupMultilinear (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    (n : ℕ) → MultilinearMap ℚ (fun _ : Fin n => A.variety.rationalCohomology 1)
      (A.variety.rationalCohomology n)
  | 0 => MultilinearMap.constOfIsEmpty ℚ _
      (AlgebraicTopology.Products.CupCohomologyAlgebra.singularCohomologyCupUnit (Betti.Scheme.schemePointSpace A.toOver))
  | n + 1 =>
      ((AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (Betti.Scheme.schemePointSpace A.toOver) n 1).compMultilinearMap
        (h1CupMultilinear A n)).uncurryRight

/-- The multilinear construction agrees with the specified iterated cup product. -/
theorem h1CupMultilinear_apply (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ)
    (v : Fin n → A.variety.rationalCohomology 1) :
    ExteriorCohomology.h1CupMultilinear A n v = A.rationalH1Cup n v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (Betti.Scheme.schemePointSpace A.toOver) n 1
      (ExteriorCohomology.h1CupMultilinear A n (Fin.init v)) (v (Fin.last n)) = _
    rw [ih]
    rfl

/-- Associativity reduces equal last factors to the cup-square identity. -/
theorem h1Cup_last_two_eq_zero (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ)
    (v : Fin (n + 2) → A.variety.rationalCohomology 1)
    (heq : v (Fin.last n).castSucc = v (Fin.last (n + 1))) :
    A.rationalH1Cup (n + 2) v = 0 := by
  have ha := AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCup_assoc (R := ℚ) (TopCat.toSSet.obj (Betti.Scheme.schemePointSpace A.toOver))
    (A.rationalH1Cup n (Fin.init (Fin.init v)))
    (v (Fin.last n).castSucc) (v (Fin.last (n + 1)))
  have hc : A.rationalH1Cup (n + 2) v =
      AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (Betti.Scheme.schemePointSpace A.toOver) n 2
        (A.rationalH1Cup n (Fin.init (Fin.init v)))
        (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (Betti.Scheme.schemePointSpace A.toOver) 1 1
          (v (Fin.last n).castSucc) (v (Fin.last (n + 1)))) := by
    simpa [ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.rationalH1Cup, AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCast, Fin.init] using ha
  rw [hc, heq, h1_cup_self, map_zero]

/-- Moving a repeated factor to the last position proves alternation. -/
theorem h1Cup_eq_zero_of_eq (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ) :
    ∀ (v : Fin n → A.variety.rationalCohomology 1) (i j : Fin n),
      v i = v j → i ≠ j → A.rationalH1Cup n v = 0 := by
  induction n with
  | zero =>
    intro v i
    exact Fin.elim0 i
  | succ n ih =>
    intro v i j hij hne
    cases n with
    | zero =>
      fin_cases i
      fin_cases j
      exact False.elim (hne rfl)
    | succ n =>
      let F : (A.variety.rationalCohomology 1) [⋀^Fin (n + 1)]→ₗ[ℚ]
          A.variety.rationalCohomology (n + 1) :=
        { ExteriorCohomology.h1CupMultilinear A (n + 1) with
          map_eq_zero_of_eq' := fun v i j hij hne => by
            change ExteriorCohomology.h1CupMultilinear A (n + 1) v = 0
            rw [h1CupMultilinear_apply]
            exact ih v i j hij hne }
      have hlast (k : Fin (n + 1))
          (hk : v k.castSucc = v (Fin.last (n + 1))) :
          A.rationalH1Cup (n + 2) v = 0 := by
        by_cases hkl : k = Fin.last n
        · exact h1Cup_last_two_eq_zero A n v (hkl ▸ hk)
        · let w : Fin (n + 2) → A.variety.rationalCohomology 1 :=
            Fin.snoc (Fin.init v ∘ Equiv.swap k (Fin.last n))
            (v (Fin.last (n + 1)))
          have hw : w (Fin.last n).castSucc = w (Fin.last (n + 1)) := by
            simpa [w, Function.comp_def, Fin.init] using hk
          have hz := h1Cup_last_two_eq_zero A n w hw
          have hs := F.map_swap (Fin.init v) hkl
          change ExteriorCohomology.h1CupMultilinear A (n + 1) (Fin.init v ∘ Equiv.swap k (Fin.last n)) =
            - ExteriorCohomology.h1CupMultilinear A (n + 1) (Fin.init v) at hs
          simp only [h1CupMultilinear_apply] at hs
          change AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (Betti.Scheme.schemePointSpace A.toOver) (n + 1) 1
            (A.rationalH1Cup (n + 1) (Fin.init w)) (w (Fin.last (n + 1))) = 0 at hz
          dsimp only [w] at hz
          rw [Fin.init_snoc, Fin.snoc_last, hs, map_neg, LinearMap.neg_apply] at hz
          exact neg_eq_zero.mp hz
      cases i using Fin.lastCases with
      | last =>
        cases j using Fin.lastCases with
        | last => exact False.elim (hne rfl)
        | cast j => exact hlast j hij.symm
      | cast i =>
        cases j using Fin.lastCases with
        | last => exact hlast i hij
        | cast j =>
          have hz : A.rationalH1Cup (n + 1) (Fin.init v) = 0 :=
            ih (Fin.init v) i j hij (fun h => hne (congrArg Fin.castSucc h))
          change AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (Betti.Scheme.schemePointSpace A.toOver) (n + 1) 1
            (A.rationalH1Cup (n + 1) (Fin.init v)) (v (Fin.last (n + 1))) = 0
          rw [hz, map_zero, LinearMap.zero_apply]

/-- The genuine iterated cup product is alternating in all degree-one factors. -/
noncomputable def h1CupAlternating (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ) :
    (A.variety.rationalCohomology 1) [⋀^Fin n]→ₗ[ℚ]
      A.variety.rationalCohomology n :=
  { ExteriorCohomology.h1CupMultilinear A n with
    map_eq_zero_of_eq' := fun v i j hij hne => by
      change ExteriorCohomology.h1CupMultilinear A n v = 0
      rw [h1CupMultilinear_apply]
      exact h1Cup_eq_zero_of_eq A n v i j hij hne }

/-- The canonical cup-induced map, constructed by the exterior universal property. -/
noncomputable def exteriorCup (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ) :
    (⋀[ℚ]^n (A.variety.rationalCohomology 1)) →ₗ[ℚ]
      A.variety.rationalCohomology n :=
  exteriorPower.alternatingMapLinearEquiv (h1CupAlternating A n)

/-- Canonical wedge normalization, including the empty wedge and its unit. -/
theorem exteriorCup_wedge (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ)
    (v : Fin n → A.variety.rationalCohomology 1) :
    exteriorCup A n (exteriorPower.ιMulti ℚ n v) = A.rationalH1Cup n v := by
  rw [exteriorCup, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  exact h1CupMultilinear_apply A n v

/-- Agreement on all decomposable wedges determines the map uniquely. -/
theorem exteriorCup_unique (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ)
    (f : (⋀[ℚ]^n (A.variety.rationalCohomology 1)) →ₗ[ℚ]
      A.variety.rationalCohomology n)
    (hf : ∀ v, f (exteriorPower.ιMulti ℚ n v) = A.rationalH1Cup n v) :
    f = exteriorCup A n := by
  apply exteriorPower.linearMap_ext
  ext v
  exact (hf v).trans (exteriorCup_wedge A n v).symm

/-- In degree one the canonical cup map is the usual exterior-power identification. -/
theorem exteriorCup_one (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    exteriorCup A 1 =
      (exteriorPower.oneEquiv ℚ (A.variety.rationalCohomology 1)).toLinearMap := by
  symm
  apply exteriorCup_unique
  intro v
  have hu := AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCupUnit_cup (R := ℚ)
    (TopCat.toSSet.obj (Betti.Scheme.schemePointSpace A.toOver)) (v 0)
  simpa [exteriorPower.oneEquiv_ιMulti, ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.rationalH1Cup,
    AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCast] using hu.symm

/-- The degree-one component is an isomorphism. -/
theorem exteriorCup_one_bijective (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    Function.Bijective (exteriorCup A 1) := by
  rw [exteriorCup_one]
  exact (exteriorPower.oneEquiv ℚ (A.variety.rationalCohomology 1)).bijective

/-- The first exterior signed piece recovers its specified degree-one subspace. -/
theorem exteriorSignedSpan_one {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (S : Bool → Submodule K V) (b : Bool) :
    ComplexMultiplication.ExteriorTypedBasis.CM.exteriorSignedSpan S 1 (ComplexMultiplication.SignSwitch.CM.signValue b) =
      (S b).comap (exteriorPower.oneEquiv K V).toLinearMap := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨ε, v, hw, hv, rfl⟩
    have hb : ε 0 = b := by
      simp only [Fin.sum_univ_one] at hw
      cases b <;> cases he : ε 0 <;> simp_all [ComplexMultiplication.SignSwitch.CM.signValue]
    change exteriorPower.oneEquiv K V (exteriorPower.ιMulti K 1 v) ∈ S b
    simpa only [exteriorPower.oneEquiv_ιMulti, hb] using hv 0
  · intro x hx
    have he : exteriorPower.ιMulti K 1 (fun _ => exteriorPower.oneEquiv K V x) = x := by
      apply (exteriorPower.oneEquiv K V).injective
      simp
    apply Submodule.subset_span
    refine ⟨fun _ => b, fun _ => exteriorPower.oneEquiv K V x, ?_, ?_, he⟩
    · simp only [Fin.sum_univ_one]
    · intro i
      exact hx

/-- Exterior scalar extension commutes with the degree-one identification. -/
theorem exteriorBaseChange_oneEquiv (U : Type*) [AddCommGroup U] [Module ℚ U]
    (x : ℂ ⊗[ℚ] (⋀[ℚ]^1 U)) :
    exteriorPower.oneEquiv ℂ (ℂ ⊗[ℚ] U) (ComplexMultiplication.ExteriorBaseChange.CM.exteriorBaseChangeEquiv ℂ U 1 x) =
      (exteriorPower.oneEquiv ℚ U).toLinearMap.baseChange ℂ x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul z u =>
    obtain ⟨v, rfl⟩ := (exteriorPower.oneEquiv ℚ U).symm.surjective u
    simp [ComplexMultiplication.ExteriorBaseChange.CM.exteriorBaseChangeEquiv_apply, exteriorPower.oneEquiv_symm_apply,
      ComplexMultiplication.ExteriorBaseChange.CM.exteriorBaseChange_tmul_ιMulti, TensorProduct.smul_tmul']

/-- The induced exterior Hodge types agree with the original types in degree one. -/
theorem mem_exteriorSignedSubspace_one (U : Type*) [AddCommGroup U] [Module ℚ U]
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U) (b : Bool)
    (x : ℂ ⊗[ℚ] (⋀[ℚ]^1 U)) :
    x ∈ H.exteriorSignedSubspace 1 (ComplexMultiplication.SignSwitch.CM.signValue b) ↔
      (exteriorPower.oneEquiv ℚ U).toLinearMap.baseChange ℂ x ∈ H.signSubspace b := by
  change x ∈ (ComplexMultiplication.ExteriorTypedBasis.CM.exteriorSignedSpan H.signSubspace 1 (ComplexMultiplication.SignSwitch.CM.signValue b)).map
    (ComplexMultiplication.ExteriorBaseChange.CM.exteriorBaseChangeEquiv ℂ U 1).symm.toLinearMap ↔ _
  rw [exteriorSignedSpan_one]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearEquiv.coe_coe] at hy
    rw [← exteriorBaseChange_oneEquiv]
    simpa only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using hy
  · intro hx
    refine ⟨ComplexMultiplication.ExteriorBaseChange.CM.exteriorBaseChangeEquiv ℂ U 1 x, ?_, ?_⟩
    · simp only [SetLike.mem_coe, Submodule.mem_comap, LinearEquiv.coe_coe]
      rw [exteriorBaseChange_oneEquiv]
      exact hx
    · exact (ComplexMultiplication.ExteriorBaseChange.CM.exteriorBaseChangeEquiv ℂ U 1).symm_apply_apply x

/-- The canonical cup map preserves and reflects the holomorphic Hodge piece. -/
theorem exteriorCup_holomorphic (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (A.variety.rationalCohomology 1))
    (hh : H.holomorphic = A.h1Holomorphic)
    (x : ℂ ⊗[ℚ] (⋀[ℚ]^1 (A.variety.rationalCohomology 1))) :
    ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace A.toOver) 1
        ((exteriorCup A 1).baseChange ℂ x) ∈ A.variety.pureBettiSubspace 1 0 ↔
      x ∈ H.exteriorPureSubspace 1 0 := by
  change _ ↔ x ∈ H.exteriorSignedSubspace 1 (ComplexMultiplication.SignSwitch.CM.signValue true)
  rw [mem_exteriorSignedSubspace_one, exteriorCup_one]
  change _ ↔ (exteriorPower.oneEquiv ℚ (A.variety.rationalCohomology 1)).toLinearMap.baseChange
    ℂ x ∈ H.holomorphic
  rw [hh]
  rfl

/-- The canonical cup map preserves and reflects the antiholomorphic Hodge piece. -/
theorem exteriorCup_antiholomorphic (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (A.variety.rationalCohomology 1))
    (ha : H.antiholomorphic = A.h1Antiholomorphic)
    (x : ℂ ⊗[ℚ] (⋀[ℚ]^1 (A.variety.rationalCohomology 1))) :
    ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace A.toOver) 1
        ((exteriorCup A 1).baseChange ℂ x) ∈ A.variety.pureBettiSubspace 0 1 ↔
      x ∈ H.exteriorPureSubspace 0 1 := by
  change _ ↔ x ∈ H.exteriorSignedSubspace 1 (ComplexMultiplication.SignSwitch.CM.signValue false)
  rw [mem_exteriorSignedSubspace_one, exteriorCup_one]
  change _ ↔ (exteriorPower.oneEquiv ℚ (A.variety.rationalCohomology 1)).toLinearMap.baseChange
    ℂ x ∈ H.antiholomorphic
  rw [ha]
  rfl

/-- Exterior powers vanish above the dimension of their source. -/
theorem exteriorPower_subsingleton_of_finrank_lt (U : Type*)
    [AddCommGroup U] [Module ℚ U] [FiniteDimensional ℚ U] (n : ℕ)
    (hn : Module.finrank ℚ U < n) : Subsingleton (⋀[ℚ]^n U) := by
  apply (Module.finrank_zero_iff (R := ℚ) (M := ⋀[ℚ]^n U)).mp
  rw [exteriorPower.finrank_eq, Nat.choose_eq_zero_of_lt hn]

/-- Above both dimension bounds the canonical cup map is an isomorphism of zero spaces. -/
theorem exteriorCup_bijective_above_dimensions (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (A.variety.rationalCohomology 1)) (n : ℕ)
    (hH : Module.finrank ℚ (A.variety.rationalCohomology 1) < n)
    (hA : 2 * A.variety.complexDimension < n) :
    Function.Bijective (exteriorCup A n) := by
  let := H.finiteDimensional
  let := exteriorPower_subsingleton_of_finrank_lt
    (A.variety.rationalCohomology 1) n hH
  let := ModuleCat.subsingleton_of_isZero
    (A.variety.rationalCohomology_isZero_of_dimension_lt n hA)
  exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩

/-- The Hodge comparison holds in every degree where the exterior source vanishes. -/
theorem exteriorCup_pure_above_h1_dimension (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (A.variety.rationalCohomology 1)) (p q : ℕ)
    (hH : Module.finrank ℚ (A.variety.rationalCohomology 1) < p + q)
    (x : ℂ ⊗[ℚ] (⋀[ℚ]^(p + q) (A.variety.rationalCohomology 1))) :
    ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace A.toOver) (p + q)
        ((exteriorCup A (p + q)).baseChange ℂ x) ∈ A.variety.pureBettiSubspace p q ↔
      x ∈ H.exteriorPureSubspace p q := by
  let := H.finiteDimensional
  let := exteriorPower_subsingleton_of_finrank_lt
    (A.variety.rationalCohomology 1) (p + q) hH
  have hx : x = 0 := Subsingleton.elim _ _
  simp [hx]

/-- Exact remaining obligations for ExteriorCohomology; this equivalence does not discharge them. -/
theorem comparison_iff (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (A.variety.rationalCohomology 1)) :
    Nonempty (ComplexMultiplication.KnownExteriorCohomology.CM.AbelianExteriorComparison A H) ↔
      (∀ n, Function.Bijective (exteriorCup A n)) ∧
      (∀ p q x,
        ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace A.toOver) (p + q)
          ((exteriorCup A (p + q)).baseChange ℂ x) ∈
            A.variety.pureBettiSubspace p q ↔ x ∈ H.exteriorPureSubspace p q) := by
  constructor
  · rintro ⟨C⟩
    have hc (n : ℕ) : (C.rational n).toLinearMap = exteriorCup A n :=
      exteriorCup_unique A n (C.rational n).toLinearMap (C.wedge n)
    constructor
    · intro n
      rw [← hc n]
      exact (C.rational n).bijective
    · intro p q x
      rw [← hc (p + q)]
      exact C.pure p q x
  · rintro ⟨hb, hp⟩
    exact ⟨{
      rational := fun n => LinearEquiv.ofBijective (exteriorCup A n) (hb n)
      wedge := exteriorCup_wedge A
      pure := hp }⟩

end OAI.AlgebraicGeometry.AbelianVariety.CupMap.Constructions.ExteriorCohomology
