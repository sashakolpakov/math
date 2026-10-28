import OAI.AlgebraicGeometry.DivisorClass.Chern.PeriodCochain
import OAI.AlgebraicGeometry.DivisorClass.Chern.Singular.Refinement
import OAI.AlgebraicGeometry.DivisorClass.Chern.LogRefinementOpen

/-! # Winding Cech -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.WindingCech

noncomputable section

section

/-!
# ChernClass: the winding class from actual continuous logarithm branches

Differences of logarithms of a nonvanishing function are integral periods.
Their degree-one Cech class maps to the same rational singular cohomology
used in the first Chern class construction. This is the exponential-sequence
class to be compared with the geometric punctured-line normalization.
-/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.DivisorClass.Chern.LogRefinementOpen.Construction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace RationalCech
section

variable {I : Type} (X : TopCat.{0}) (U : I → Opens X)

abbrev BranchCochain := Rational.Cech.RationalCech.CechCochain (LogCech.RationalCech.continuousComplexPresheaf X) U 0

/-- Exponentials of these branches agree on overlaps. -/
def BranchCompatibility (b : BranchCochain X U) : Prop :=
  ∀ a x, Complex.exp (Rational.Cech.RationalCech.cechDelta (LogCech.RationalCech.continuousComplexPresheaf X) U 0 b a x) = 1

theorem branchDelta_exp (b : BranchCochain X U) (a : Fin 2 → I) (x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) :
    Complex.exp (Rational.Cech.RationalCech.cechDelta (LogCech.RationalCech.continuousComplexPresheaf X) U 0 b a x) =
      Complex.exp (b (a ∘ (0 : Fin 2).succAbove)
        ⟨x.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a _ x.property⟩) /
      Complex.exp (b (a ∘ (1 : Fin 2).succAbove)
        ⟨x.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a _ x.property⟩) := by
  rw [Rational.Cech.RationalCech.cechDelta_apply, Fin.sum_univ_two]
  change Complex.exp ((1 : ℤ) • b (a ∘ (0 : Fin 2).succAbove) _ +
    (-1 : ℤ) • b (a ∘ (1 : Fin 2).succAbove) _) = _
  rw [one_zsmul, neg_one_zsmul, ← sub_eq_add_neg, Complex.exp_sub]
  rfl

/-- Branches of one actual global function satisfy the overlap condition. -/
theorem branchCompatibility_of_global (g : C(X, ℂ)) (hg : ∀ x, g x ≠ 0)
    (b : BranchCochain X U)
    (hb : ∀ (a : Fin 1 → I) (x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a), Complex.exp (b a x) = g x.val) :
    BranchCompatibility X U b := by
  intro a x
  rw [branchDelta_exp, hb, hb]
  exact div_self (hg x.val)

/-- The rationalization of the actual integer differences of branches. -/
def branchWindingCech (b : BranchCochain X U) (h : BranchCompatibility X U b) :
    Rational.Cech.RationalCech.CechCochain (Cech.Obj.RationalCech.locallyConstantPresheaf X) U 1 :=
  PeriodCochain.RationalCech.periodCochain X U 1 (Rational.Cech.RationalCech.cechDelta (LogCech.RationalCech.continuousComplexPresheaf X) U 0 b) h

theorem periodMap_branchWindingCech (b : BranchCochain X U) (h : BranchCompatibility X U b) :
    Rational.Cech.RationalCech.cechCoefficientMap U (LogCech.RationalCech.periodMap X) 1 (branchWindingCech X U b h) =
      Rational.Cech.RationalCech.cechDelta (LogCech.RationalCech.continuousComplexPresheaf X) U 0 b :=
  PeriodCochain.RationalCech.periodMap_periodCochain X U 1 _ h

theorem branchWindingCech_closed (b : BranchCochain X U) (h : BranchCompatibility X U b) :
    Rational.Cech.RationalCech.cechDelta (Cech.Obj.RationalCech.locallyConstantPresheaf X) U 1 (branchWindingCech X U b h) = 0 :=
  PeriodCochain.RationalCech.periodCochain_closed X U 1 _ h (Rational.Cech.RationalCech.cechDelta_squared (LogCech.RationalCech.continuousComplexPresheaf X) U 0 b)

def branchWindingCocycle (b : BranchCochain X U) (h : BranchCompatibility X U b) :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (Rational.Cech.RationalCech.cechComplex (Cech.Obj.RationalCech.locallyConstantPresheaf X) U) 1 :=
  ⟨branchWindingCech X U b h, by
    rw [AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff, Rational.Cech.RationalCech.cechComplex_d]
    exact branchWindingCech_closed X U b h⟩

/-- The actual rational singular winding class determined by logarithm branches. -/
def branchWindingClass (hU : ∀ x : X, ∃ i, x ∈ U i)
    (b : BranchCochain X U) (h : BranchCompatibility X U b) :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X 1 :=
  Cech.Obj.RationalCech.singularClassOfCechCocycle X U hU 1 (branchWindingCocycle X U b h)

/-- Two sets of branches of the same function differ by integral degree-zero periods. -/
theorem branchWindingClass_branches_independent (hU : ∀ x : X, ∃ i, x ∈ U i)
    (b b' : BranchCochain X U) (h : BranchCompatibility X U b) (h' : BranchCompatibility X U b')
    (he : ∀ a x, Complex.exp (b a x) = Complex.exp (b' a x)) :
    branchWindingClass X U hU b h = branchWindingClass X U hU b' h' := by
  have hp : ∀ a x, Complex.exp ((b - b') a x) = 1 := by
    intro a x
    change Complex.exp (b a x - b' a x) = 1
    rw [Complex.exp_sub, he, div_self (Complex.exp_ne_zero _)]
  apply Cech.Obj.RationalCech.singularClassOfCechCocycle_eq_of_boundary X U hU 0
    (branchWindingCocycle X U b h) (branchWindingCocycle X U b' h')
    (PeriodCochain.RationalCech.periodCochain X U 0 (b - b') hp)
  apply LogCech.RationalCech.periodCechMap_injective X U 1
  rw [Rational.Cech.RationalCech.cechCoefficientMap_delta, PeriodCochain.RationalCech.periodMap_periodCochain, map_sub, map_sub]
  change _ = Rational.Cech.RationalCech.cechCoefficientMap U (LogCech.RationalCech.periodMap X) 1 (branchWindingCech X U b h) -
    Rational.Cech.RationalCech.cechCoefficientMap U (LogCech.RationalCech.periodMap X) 1 (branchWindingCech X U b' h')
  rw [periodMap_branchWindingCech, periodMap_branchWindingCech]

end

variable (X : TopCat.{0}) (g : C(X, ℂ))

/-- The explicit slit-plane neighborhoods on which the function has a logarithm. -/
def functionLogCover (p : X) : Opens X :=
  ⟨Logarithms.Construction.logarithmNeighborhood g p, Logarithms.Construction.isOpen_logarithmNeighborhood g p⟩

theorem functionLogCover_covers (hg : ∀ x, g x ≠ 0) (x : X) :
    ∃ p, x ∈ functionLogCover X g p := ⟨x, Logarithms.Construction.mem_logarithmNeighborhood g x (hg x)⟩

/-- The explicit continuous local branches of the actual function. -/
def functionLogBranches : BranchCochain X (functionLogCover X g) :=
  fun a => (Logarithms.Construction.localLogarithm g (a 0)).comp
    (LogRefinementOpen.Construction.openInclusionMap (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le (functionLogCover X g) a 0))

theorem functionLogBranches_exp (hg : ∀ x, g x ≠ 0) (a : Fin 1 → X)
    (x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (functionLogCover X g) a) :
    Complex.exp (functionLogBranches X g a x) = g x.val :=
  Logarithms.Construction.exp_localLogarithm g (a 0) (hg (a 0)) _

theorem functionLogBranches_compatible (hg : ∀ x, g x ≠ 0) :
    BranchCompatibility X (functionLogCover X g) (functionLogBranches X g) :=
  branchCompatibility_of_global X (functionLogCover X g) g hg
    (functionLogBranches X g) (functionLogBranches_exp X g hg)

/-- The exponential-sequence winding class of an actual nonvanishing function. -/
def logarithmicWindingClass (hg : ∀ x, g x ≠ 0) : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X 1 :=
  branchWindingClass X (functionLogCover X g) (functionLogCover_covers X g hg)
    (functionLogBranches X g) (functionLogBranches_compatible X g hg)

end RationalCech

end

section

/-!
# ChernClass: independence of the winding class from its logarithm cover

Restriction preserves the actual integral-period cocycle. Any local branches
of a nonvanishing function therefore compute its canonical singular class.
-/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace RationalCech

variable {I J : Type} (X : TopCat.{0})
variable (U : I → Opens X) (V : J → Opens X) (r : J → I) (hr : ∀ j, V j ≤ U (r j))

abbrev refineBranches (b : BranchCochain X U) : BranchCochain X V :=
  Rational.Cech.RationalCech.cechRefinementMap (LogCech.RationalCech.continuousComplexPresheaf X) U V r hr 0 b

theorem branchCompatibility_refinement (b : BranchCochain X U)
    (h : BranchCompatibility X U b) :
    BranchCompatibility X V (refineBranches X U V r hr b) := by
  intro a x
  change Complex.exp (Rational.Cech.RationalCech.cechDelta (LogCech.RationalCech.continuousComplexPresheaf X) V 0
    (Rational.Cech.RationalCech.cechRefinementMap (LogCech.RationalCech.continuousComplexPresheaf X) U V r hr 0 b) a x) = 1
  rw [← Rational.Cech.RationalCech.cechRefinementMap_delta]
  exact h (r ∘ a) ⟨x.val, Rational.Cech.RationalCech.cechIntersection_refinement_le U V r hr a x.property⟩

theorem branchWindingCech_refinement (b : BranchCochain X U)
    (h : BranchCompatibility X U b) :
    branchWindingCech X V (refineBranches X U V r hr b)
        (branchCompatibility_refinement X U V r hr b h) =
      Rational.Cech.RationalCech.cechRefinementMap (Cech.Obj.RationalCech.locallyConstantPresheaf X) U V r hr 1 (branchWindingCech X U b h) := by
  apply LogCech.RationalCech.periodCechMap_injective X V 1
  rw [Cech.Refinement.RationalCech.cechCoefficientMap_refinement, periodMap_branchWindingCech,
    periodMap_branchWindingCech, Rational.Cech.RationalCech.cechRefinementMap_delta]

theorem branchWindingClass_refinement
    (hU : ∀ x : X, ∃ i, x ∈ U i) (hV : ∀ x : X, ∃ j, x ∈ V j)
    (b : BranchCochain X U) (h : BranchCompatibility X U b) :
    branchWindingClass X V hV (refineBranches X U V r hr b)
        (branchCompatibility_refinement X U V r hr b h) =
      branchWindingClass X U hU b h := by
  have hc : branchWindingCocycle X V (refineBranches X U V r hr b)
      (branchCompatibility_refinement X U V r hr b h) =
    AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (Rational.Cech.RationalCech.cechRefinement (Cech.Obj.RationalCech.locallyConstantPresheaf X) U V r hr) 1
      (branchWindingCocycle X U b h) := by
    apply Subtype.ext
    exact branchWindingCech_refinement X U V r hr b h
  unfold branchWindingClass
  rw [hc]
  exact Singular.Refinement.RationalCech.singularClassOfCechCocycle_refinement X U V r hr hU hV 1 _

/-- Two arbitrary logarithm covers of the same function give the same class. -/
theorem branchWindingClass_cover_independent
    (hU : ∀ x : X, ∃ i, x ∈ U i) (hV : ∀ x : X, ∃ j, x ∈ V j)
    (g : C(X, ℂ)) (b : BranchCochain X U) (b' : BranchCochain X V)
    (h : BranchCompatibility X U b) (h' : BranchCompatibility X V b')
    (hb : ∀ a x, Complex.exp (b a x) = g x.val)
    (hb' : ∀ a x, Complex.exp (b' a x) = g x.val) :
    branchWindingClass X U hU b h = branchWindingClass X V hV b' h' := by
  let W : I × J → Opens X := fun a => U a.1 ⊓ V a.2
  have hW : ∀ x, ∃ a, x ∈ W a := by
    intro x
    obtain ⟨i, hi⟩ := hU x
    obtain ⟨j, hj⟩ := hV x
    exact ⟨(i, j), hi, hj⟩
  have hWU : ∀ a, W a ≤ U a.1 := fun _ => inf_le_left
  have hWV : ∀ a, W a ≤ V a.2 := fun _ => inf_le_right
  have hc : branchWindingClass X W hW (refineBranches X U W Prod.fst hWU b)
      (branchCompatibility_refinement X U W Prod.fst hWU b h) =
    branchWindingClass X W hW (refineBranches X V W Prod.snd hWV b')
      (branchCompatibility_refinement X V W Prod.snd hWV b' h') := by
    apply branchWindingClass_branches_independent
    intro a x
    exact (hb (Prod.fst ∘ a)
      ⟨x.val, Rational.Cech.RationalCech.cechIntersection_refinement_le U W Prod.fst hWU a x.property⟩).trans
      (hb' (Prod.snd ∘ a)
        ⟨x.val, Rational.Cech.RationalCech.cechIntersection_refinement_le V W Prod.snd hWV a x.property⟩).symm
  exact (branchWindingClass_refinement X U W Prod.fst hWU hU hW b h).symm.trans
    (hc.trans (branchWindingClass_refinement X V W Prod.snd hWV hV hW b' h'))

/-- Any genuine cover with logarithm branches computes the canonical class. -/
theorem branchWindingClass_eq_logarithmicWindingClass
    (hU : ∀ x : X, ∃ i, x ∈ U i) (g : C(X, ℂ)) (hg : ∀ x, g x ≠ 0)
    (b : BranchCochain X U) (h : BranchCompatibility X U b)
    (hb : ∀ a x, Complex.exp (b a x) = g x.val) :
    branchWindingClass X U hU b h = logarithmicWindingClass X g hg :=
  branchWindingClass_cover_independent X U (functionLogCover X g) hU
    (functionLogCover_covers X g hg) g b (functionLogBranches X g) h
    (functionLogBranches_compatible X g hg) hb (functionLogBranches_exp X g hg)

end RationalCech

end

/-!
# ChernClass: multiplicity arithmetic for the actual logarithmic winding class

Products add winding, integer powers multiply it, and global logarithms have
zero winding. In particular a local factor with a continuous logarithm does
not change the winding multiplicity of a local equation.
-/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace RationalCech

variable {I : Type} (X : TopCat.{0}) (U : I → Opens X)

theorem branchCompatibility_add (b c : BranchCochain X U)
    (hb : BranchCompatibility X U b) (hc : BranchCompatibility X U c) :
    BranchCompatibility X U (b + c) := by
  intro a x
  rw [map_add]
  change Complex.exp (Rational.Cech.RationalCech.cechDelta (LogCech.RationalCech.continuousComplexPresheaf X) U 0 b a x +
    Rational.Cech.RationalCech.cechDelta (LogCech.RationalCech.continuousComplexPresheaf X) U 0 c a x) = 1
  rw [Complex.exp_add, hb, hc, mul_one]

theorem branchCompatibility_zsmul (b : BranchCochain X U)
    (hb : BranchCompatibility X U b) (m : ℤ) : BranchCompatibility X U (m • b) := by
  intro a x
  rw [map_zsmul]
  change Complex.exp (m • Rational.Cech.RationalCech.cechDelta (LogCech.RationalCech.continuousComplexPresheaf X) U 0 b a x) = 1
  rw [zsmul_eq_mul, Complex.exp_int_mul, hb, one_zpow]

theorem branchWindingCech_add (b c : BranchCochain X U)
    (hb : BranchCompatibility X U b) (hc : BranchCompatibility X U c) :
    branchWindingCech X U (b + c) (branchCompatibility_add X U b c hb hc) =
      branchWindingCech X U b hb + branchWindingCech X U c hc := by
  apply LogCech.RationalCech.periodCechMap_injective X U 1
  rw [map_add, periodMap_branchWindingCech, periodMap_branchWindingCech,
    periodMap_branchWindingCech, map_add]

theorem branchWindingCech_zsmul (b : BranchCochain X U)
    (hb : BranchCompatibility X U b) (m : ℤ) :
    branchWindingCech X U (m • b) (branchCompatibility_zsmul X U b hb m) =
      m • branchWindingCech X U b hb := by
  apply LogCech.RationalCech.periodCechMap_injective X U 1
  rw [map_zsmul, periodMap_branchWindingCech, periodMap_branchWindingCech, map_zsmul]

theorem branchWindingClass_add (hU : ∀ x : X, ∃ i, x ∈ U i)
    (b c : BranchCochain X U) (hb : BranchCompatibility X U b) (hc : BranchCompatibility X U c) :
    branchWindingClass X U hU (b + c) (branchCompatibility_add X U b c hb hc) =
      branchWindingClass X U hU b hb + branchWindingClass X U hU c hc := by
  have h : branchWindingCocycle X U (b + c) (branchCompatibility_add X U b c hb hc) =
    branchWindingCocycle X U b hb + branchWindingCocycle X U c hc := by
    apply Subtype.ext
    exact branchWindingCech_add X U b c hb hc
  unfold branchWindingClass Cech.Obj.RationalCech.singularClassOfCechCocycle
  rw [h, map_add, map_add]

theorem branchWindingClass_zsmul (hU : ∀ x : X, ∃ i, x ∈ U i)
    (b : BranchCochain X U) (hb : BranchCompatibility X U b) (m : ℤ) :
    branchWindingClass X U hU (m • b) (branchCompatibility_zsmul X U b hb m) =
      m • branchWindingClass X U hU b hb := by
  have h : branchWindingCocycle X U (m • b) (branchCompatibility_zsmul X U b hb m) =
    m • branchWindingCocycle X U b hb := by
    apply Subtype.ext
    exact branchWindingCech_zsmul X U b hb m
  unfold branchWindingClass Cech.Obj.RationalCech.singularClassOfCechCocycle
  rw [h, map_zsmul, map_zsmul]

/-- Restrict one actual global logarithm to every chart. -/
def globalBranches (l : C(X, ℂ)) : BranchCochain X U :=
  fun _ => l.comp ⟨Subtype.val, continuous_subtype_val⟩

theorem globalBranches_delta (l : C(X, ℂ)) :
    Rational.Cech.RationalCech.cechDelta (LogCech.RationalCech.continuousComplexPresheaf X) U 0 (globalBranches X U l) = 0 := by
  funext a
  apply ContinuousMap.ext
  intro x
  rw [Rational.Cech.RationalCech.cechDelta_apply, Fin.sum_univ_two]
  change (1 : ℤ) • l x.val + (-1 : ℤ) • l x.val = 0
  simp

theorem globalBranches_compatible (l : C(X, ℂ)) :
    BranchCompatibility X U (globalBranches X U l) := by
  intro a x
  rw [globalBranches_delta]
  exact Complex.exp_zero

theorem branchWindingClass_globalBranches (hU : ∀ x : X, ∃ i, x ∈ U i)
    (l : C(X, ℂ)) :
    branchWindingClass X U hU (globalBranches X U l) (globalBranches_compatible X U l) = 0 := by
  have h : branchWindingCocycle X U (globalBranches X U l)
      (globalBranches_compatible X U l) = 0 := by
    apply Subtype.ext
    change branchWindingCech X U (globalBranches X U l) (globalBranches_compatible X U l) = 0
    apply LogCech.RationalCech.periodCechMap_injective X U 1
    rw [periodMap_branchWindingCech, globalBranches_delta, map_zero]
  unfold branchWindingClass Cech.Obj.RationalCech.singularClassOfCechCocycle
  rw [h, map_zero, map_zero]

/-- A global continuous logarithm is an actual zero-winding certificate. -/
theorem logarithmicWindingClass_eq_zero_of_log (g l : C(X, ℂ))
    (hg : ∀ x, g x ≠ 0) (hl : ∀ x, Complex.exp (l x) = g x) :
    logarithmicWindingClass X g hg = 0 := by
  rw [← branchWindingClass_eq_logarithmicWindingClass X (functionLogCover X g)
    (functionLogCover_covers X g hg) g hg (globalBranches X (functionLogCover X g) l)
    (globalBranches_compatible X (functionLogCover X g) l) (fun a x => hl x.val)]
  exact branchWindingClass_globalBranches X _ _ l

/-- Pointwise multiplication of actual nonvanishing functions adds winding. -/
theorem logarithmicWindingClass_mul (f g : C(X, ℂ))
    (hf : ∀ x, f x ≠ 0) (hg : ∀ x, g x ≠ 0) :
    logarithmicWindingClass X (f * g) (fun x => mul_ne_zero (hf x) (hg x)) =
      logarithmicWindingClass X f hf + logarithmicWindingClass X g hg := by
  let F := functionLogCover X f
  let G := functionLogCover X g
  let W : X × X → Opens X := fun a => F a.1 ⊓ G a.2
  have hW : ∀ x, ∃ a, x ∈ W a := fun x =>
    ⟨(x, x), Logarithms.Construction.mem_logarithmNeighborhood f x (hf x),
      Logarithms.Construction.mem_logarithmNeighborhood g x (hg x)⟩
  have hWF : ∀ a, W a ≤ F a.1 := fun _ => inf_le_left
  have hWG : ∀ a, W a ≤ G a.2 := fun _ => inf_le_right
  let b := refineBranches X F W Prod.fst hWF (functionLogBranches X f)
  let c := refineBranches X G W Prod.snd hWG (functionLogBranches X g)
  have hb := branchCompatibility_refinement X F W Prod.fst hWF
    (functionLogBranches X f) (functionLogBranches_compatible X f hf)
  have hc := branchCompatibility_refinement X G W Prod.snd hWG
    (functionLogBranches X g) (functionLogBranches_compatible X g hg)
  have hbf : ∀ a x, Complex.exp (b a x) = f x.val := fun a x =>
    functionLogBranches_exp X f hf (Prod.fst ∘ a)
      ⟨x.val, Rational.Cech.RationalCech.cechIntersection_refinement_le F W Prod.fst hWF a x.property⟩
  have hcg : ∀ a x, Complex.exp (c a x) = g x.val := fun a x =>
    functionLogBranches_exp X g hg (Prod.snd ∘ a)
      ⟨x.val, Rational.Cech.RationalCech.cechIntersection_refinement_le G W Prod.snd hWG a x.property⟩
  have hbc : ∀ a x, Complex.exp ((b + c) a x) = (f * g) x.val := by
    intro a x
    change Complex.exp (b a x + c a x) = f x.val * g x.val
    rw [Complex.exp_add, hbf, hcg]
  rw [← branchWindingClass_eq_logarithmicWindingClass X W hW (f * g) _
    (b + c) (branchCompatibility_add X W b c hb hc) hbc,
    branchWindingClass_add X W hW b c hb hc,
    branchWindingClass_eq_logarithmicWindingClass X W hW f hf b hb hbf,
    branchWindingClass_eq_logarithmicWindingClass X W hW g hg c hc hcg]

/-- An integer power of a nonvanishing function, supplied as an actual
continuous map, has that integer times the original winding class. -/
theorem logarithmicWindingClass_int_power (g f : C(X, ℂ))
    (hg : ∀ x, g x ≠ 0) (hf : ∀ x, f x ≠ 0) (m : ℤ)
    (hfg : ∀ x, f x = g x ^ m) :
    logarithmicWindingClass X f hf = m • logarithmicWindingClass X g hg := by
  let V := functionLogCover X g
  let b := functionLogBranches X g
  have hb := functionLogBranches_compatible X g hg
  have he : ∀ a x, Complex.exp ((m • b) a x) = f x.val := by
    intro a x
    change Complex.exp (m • b a x) = f x.val
    rw [zsmul_eq_mul, Complex.exp_int_mul, functionLogBranches_exp X g hg, hfg]
  rw [← branchWindingClass_eq_logarithmicWindingClass X V
    (functionLogCover_covers X g hg) f hf (m • b) (branchCompatibility_zsmul X V b hb m) he,
    branchWindingClass_zsmul X V (functionLogCover_covers X g hg) b hb m]
  rfl

/-- The integer power is continuous on the actual nonvanishing locus. -/
def nonvanishingPower (g : C(X, ℂ)) (hg : ∀ x, g x ≠ 0) (m : ℤ) : C(X, ℂ) :=
  ⟨fun x => g x ^ m, g.continuous.zpow₀ m (fun x => Or.inl (hg x))⟩

/-- The winding multiplicity of a local equation times a logarithmically
trivial unit. Negative integers include poles. -/
theorem logarithmicWindingClass_log_unit_power (g f l : C(X, ℂ))
    (hg : ∀ x, g x ≠ 0) (hf : ∀ x, f x ≠ 0) (m : ℤ)
    (hfg : ∀ x, f x = Complex.exp (l x) * g x ^ m) :
    logarithmicWindingClass X f hf = m • logarithmicWindingClass X g hg := by
  let u : C(X, ℂ) := ⟨fun x => Complex.exp (l x), Complex.continuous_exp.comp l.continuous⟩
  let v := nonvanishingPower X g hg m
  have hu : ∀ x, u x ≠ 0 := fun x => Complex.exp_ne_zero (l x)
  have hv : ∀ x, v x ≠ 0 := fun x => zpow_ne_zero m (hg x)
  have hfun : f = u * v := ContinuousMap.ext hfg
  subst f
  rw [logarithmicWindingClass_mul X u v hu hv,
    logarithmicWindingClass_eq_zero_of_log X u l hu (fun _ => rfl), zero_add]
  exact logarithmicWindingClass_int_power X g v hg hv m (fun _ => rfl)

end RationalCech

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.WindingCech
