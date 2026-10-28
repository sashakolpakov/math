import OAI.Topology.Euclidean.IncreasingCover
import OAI.Topology.Euclidean.Telescope

/-! # Increasing Cochains -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.IncreasingCochains

noncomputable section

/-!
# Singular cochains on an increasing open cover

A singular simplex has compact image, so it lies in one member of an
increasing open cover. Compatible cochains on the members therefore define
a unique cochain on the whole space. All restrictions below are the actual
singular pullbacks along open-subspace inclusions.
-/

open _root_.CategoryTheory Opposite _root_.TopologicalSpace
open OAI.Topology.Euclidean.IncreasingCover.Globalization
open scoped Simplicial

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [Ring R] (M : ModuleCat.{0} R) {X : TopCat.{0}}
variable (U : ℕ → Opens X) (hmono : Monotone U)

/-- The actual inclusion between two members of an increasing open cover. -/
def increasingOpenInclusion {i j : ℕ} (hij : i ≤ j) :
    TopCat.of (U i) ⟶ TopCat.of (U j) :=
  (Opens.toTopCat X).map (homOfLE (hmono hij))

@[simp]
theorem increasingOpenInclusion_self (i : ℕ) :
    increasingOpenInclusion U hmono (le_refl i) = 𝟙 (TopCat.of (U i)) := by
  ext x
  rfl

@[reassoc]
theorem increasingOpenInclusion_comp {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    increasingOpenInclusion U hmono hij ≫ increasingOpenInclusion U hmono hjk =
      increasingOpenInclusion U hmono (hij.trans hjk) := by
  ext x
  rfl

@[reassoc]
theorem increasingOpenInclusion_to_global {i j : ℕ} (hij : i ≤ j) :
    increasingOpenInclusion U hmono hij ≫ (U j).inclusion' = (U i).inclusion' := by
  ext x
  rfl

/-- The cochain complexes of the members of the open cover. -/
abbrev increasingCochainTower (i : ℕ) : CochainComplex (ModuleCat.{0} R) ℕ :=
  Basic.singularCochains M (TopCat.of (U i))

/-- Pullback between any two ordered members of the open cover. -/
def increasingCochainPullback {i j : ℕ} (hij : i ≤ j) :
    increasingCochainTower M U j ⟶ increasingCochainTower M U i :=
  Functor.singularPullback M (increasingOpenInclusion U hmono hij)

/-- The adjacent transition morphisms of the cochain tower. -/
def increasingCochainTransition (i : ℕ) :
    increasingCochainTower M U (i + 1) ⟶ increasingCochainTower M U i :=
  increasingCochainPullback M U hmono (Nat.le_succ i)

/-- Restriction of a global cochain to a member of the open cover. -/
def increasingCochainRestriction (i : ℕ) :
    Basic.singularCochains M X ⟶ increasingCochainTower M U i :=
  Functor.singularPullback M (U i).inclusion'

/-- Restriction evaluates a local simplex through its actual global image. -/
theorem increasingCochainRestriction_evaluation (i n : ℕ)
    (c : (Basic.singularCochains M X).X n) (s : Basic.singularSimplices (TopCat.of (U i)) n) :
    Coefficients.simplicialEvaluation (TopCat.toSSet.obj (TopCat.of (U i))) M s
        ((increasingCochainRestriction M U i).f n c) =
      Coefficients.simplicialEvaluation (TopCat.toSSet.obj X) M
        ((TopCat.toSSet.map (U i).inclusion').app (op ⦋n⦌) s) c :=
  Formulas.evaluation_pullback_apply M (TopCat.toSSet.map (U i).inclusion') c s

@[simp]
theorem increasingCochainPullback_self (i : ℕ) :
    increasingCochainPullback M U hmono (le_refl i) = 𝟙 (increasingCochainTower M U i) := by
  rw [increasingCochainPullback, increasingOpenInclusion_self, Functor.singularPullback_id]

@[reassoc]
theorem increasingCochainPullback_comp {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    increasingCochainPullback M U hmono hjk ≫ increasingCochainPullback M U hmono hij =
      increasingCochainPullback M U hmono (hij.trans hjk) := by
  simpa only [increasingCochainPullback, increasingOpenInclusion_comp] using
    (Functor.singularPullback_comp M (increasingOpenInclusion U hmono hij)
      (increasingOpenInclusion U hmono hjk)).symm

@[reassoc]
theorem increasingCochainRestriction_pullback {i j : ℕ} (hij : i ≤ j) :
    increasingCochainRestriction M U j ≫ increasingCochainPullback M U hmono hij =
      increasingCochainRestriction M U i := by
  simpa only [increasingCochainRestriction, increasingCochainPullback,
    increasingOpenInclusion_to_global] using
    (Functor.singularPullback_comp M (increasingOpenInclusion U hmono hij) (U j).inclusion').symm

/-- Adjacent compatibility implies compatibility with every later member. -/
theorem increasingCochain_compatible_of_adjacent (n : ℕ)
    (c : ∀ i, (increasingCochainTower M U i).X n)
    (hc : ∀ i, c i = (increasingCochainTransition M U hmono i).f n (c (i + 1)))
    {i j : ℕ} (hij : i ≤ j) :
    c i = (increasingCochainPullback M U hmono hij).f n (c j) := by
  induction j, hij using Nat.le_induction with
  | base => simp only [increasingCochainPullback_self, HomologicalComplex.id_f, ModuleCat.id_apply]
  | succ j hij ih =>
      rw [ih, hc j]
      exact congrArg (fun f : increasingCochainTower M U (j + 1) ⟶
        increasingCochainTower M U i => f.f n (c (j + 1)))
        (increasingCochainPullback_comp M U hmono hij (Nat.le_succ j))

/-- An open inclusion is injective on genuine singular simplices. -/
theorem singularOpenInclusion_injective (V : Opens X) (n : ℕ) :
    Function.Injective ((TopCat.toSSet.map V.inclusion').app (op ⦋n⦌)) := by
  intro s t h
  apply (Coefficients.singularSimplicesEquivContinuousMap (TopCat.of V) n).injective
  ext z
  exact congrArg (fun σ : Basic.singularSimplices X n =>
    Coefficients.singularSimplicesEquivContinuousMap X n σ z) h

@[simp]
theorem increasingOpenInclusion_simplex_to_global {i j n : ℕ} (hij : i ≤ j)
    (s : Basic.singularSimplices (TopCat.of (U i)) n) :
    (TopCat.toSSet.map (U j).inclusion').app (op ⦋n⦌)
        ((TopCat.toSSet.map (increasingOpenInclusion U hmono hij)).app (op ⦋n⦌) s) =
      (TopCat.toSSet.map (U i).inclusion').app (op ⦋n⦌) s := by
  apply (Coefficients.singularSimplicesEquivContinuousMap X n).injective
  rfl

/-- Compatible cochains give the same value on any two local lifts of the
same global simplex. -/
theorem increasingCochain_evaluation_independent (n : ℕ)
    (c : ∀ i, (increasingCochainTower M U i).X n)
    (hc : ∀ i, c i = (increasingCochainTransition M U hmono i).f n (c (i + 1)))
    {i j : ℕ} (s : Basic.singularSimplices (TopCat.of (U i)) n)
    (t : Basic.singularSimplices (TopCat.of (U j)) n)
    (hst : (TopCat.toSSet.map (U i).inclusion').app (op ⦋n⦌) s =
      (TopCat.toSSet.map (U j).inclusion').app (op ⦋n⦌) t) :
    Coefficients.simplicialEvaluation (TopCat.toSSet.obj (TopCat.of (U i))) M s (c i) =
      Coefficients.simplicialEvaluation (TopCat.toSSet.obj (TopCat.of (U j))) M t (c j) := by
  rw [increasingCochain_compatible_of_adjacent M U hmono n c hc (le_max_left i j),
    increasingCochain_compatible_of_adjacent M U hmono n c hc (le_max_right i j)]
  change Coefficients.simplicialEvaluation _ M s
      ((Functor.simplicialPullback M (TopCat.toSSet.map
        (increasingOpenInclusion U hmono (le_max_left i j)))).f n (c (max i j))) =
    Coefficients.simplicialEvaluation _ M t
      ((Functor.simplicialPullback M (TopCat.toSSet.map
        (increasingOpenInclusion U hmono (le_max_right i j)))).f n (c (max i j)))
  rw [Formulas.evaluation_pullback_apply, Formulas.evaluation_pullback_apply]
  apply congrArg (fun u : Basic.singularSimplices (TopCat.of (U (max i j))) n =>
    Coefficients.simplicialEvaluation (TopCat.toSSet.obj (TopCat.of (U (max i j)))) M u (c (max i j)))
  apply singularOpenInclusion_injective (U (max i j)) n
  simpa only [increasingOpenInclusion_simplex_to_global] using hst

/-- Actual singular cochains are determined by their values on all simplices. -/
theorem singularCochain_eq_of_evaluation_eq (n : ℕ)
    {a b : (Basic.singularCochains M X).X n}
    (h : ∀ s : Basic.singularSimplices X n,
      Coefficients.simplicialEvaluation (TopCat.toSSet.obj X) M s a =
        Coefficients.simplicialEvaluation (TopCat.toSSet.obj X) M s b) : a = b := by
  apply (Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) M n).toLinearEquiv.injective
  change (Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) M n).hom a =
    (Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) M n).hom b
  funext s
  exact (Coefficients.degreewiseFunctionIso_hom_apply (TopCat.toSSet.obj X) M a s).trans
    ((h s).trans (Coefficients.degreewiseFunctionIso_hom_apply (TopCat.toSSet.obj X) M b s).symm)

/-- Restriction between cover members is surjective in every cochain degree:
an arbitrary function on the smaller set of simplices extends to the larger. -/
theorem increasingCochainPullback_f_surjective {i j : ℕ} (hij : i ≤ j) (n : ℕ) :
    Function.Surjective ((increasingCochainPullback M U hmono hij).f n) := by
  let f : Basic.singularSimplices (TopCat.of (U i)) n → Basic.singularSimplices (TopCat.of (U j)) n :=
    (TopCat.toSSet.map (increasingOpenInclusion U hmono hij)).app (op ⦋n⦌)
  have hf : Function.Injective f := by
    intro s t h
    apply singularOpenInclusion_injective (U i) n
    have hh := congrArg
      ((TopCat.toSSet.map (U j).inclusion').app (op ⦋n⦌)) h
    simpa only [f, increasingOpenInclusion_simplex_to_global] using hh
  intro c
  let φ := Function.extend f
    ((Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj (TopCat.of (U i))) M n).hom c) (fun _ => 0)
  refine ⟨(Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj (TopCat.of (U j))) M n).inv φ, ?_⟩
  apply singularCochain_eq_of_evaluation_eq M n
  intro s
  change Coefficients.simplicialEvaluation _ M s
    ((Functor.simplicialPullback M (TopCat.toSSet.map
      (increasingOpenInclusion U hmono hij))).f n _) = _
  rw [Formulas.evaluation_pullback_apply, ← Coefficients.degreewiseFunctionIso_hom_apply, Iso.inv_hom_id_apply]
  exact (hf.extend_apply _ _ s).trans
    (Coefficients.degreewiseFunctionIso_hom_apply (TopCat.toSSet.obj (TopCat.of (U i))) M c s)

/-- Every adjacent transition of the actual singular cochain tower is
surjective in every degree. -/
theorem increasingCochainTransition_f_surjective (i n : ℕ) :
    Function.Surjective ((increasingCochainTransition M U hmono i).f n) :=
  increasingCochainPullback_f_surjective M U hmono (Nat.le_succ i) n

variable (hcover : (⨆ i, U i) = ⊤)

/-- Choose a cover member containing a singular simplex, using compactness. -/
def increasingSimplexIndex {n : ℕ} (s : Basic.singularSimplices X n) : ℕ :=
  (Topology.Euclidean.IncreasingCover.Globalization.exists_singularSimplex_lift U hmono hcover s).choose

/-- The chosen actual simplex in the chosen cover member. -/
def increasingSimplexLift {n : ℕ} (s : Basic.singularSimplices X n) :
    Basic.singularSimplices (TopCat.of (U (increasingSimplexIndex U hmono hcover s))) n :=
  (Topology.Euclidean.IncreasingCover.Globalization.exists_singularSimplex_lift U hmono hcover s).choose_spec.choose

@[simp]
theorem increasingSimplexLift_spec {n : ℕ} (s : Basic.singularSimplices X n) :
    (TopCat.toSSet.map (U (increasingSimplexIndex U hmono hcover s)).inclusion').app
      (op ⦋n⦌) (increasingSimplexLift U hmono hcover s) = s :=
  (Topology.Euclidean.IncreasingCover.Globalization.exists_singularSimplex_lift U hmono hcover s).choose_spec.choose_spec

/-- Evaluate a family on the chosen local lifts to obtain a global cochain.
Compatibility will make this construction independent of the chosen lifts. -/
def increasingCochainGlue (n : ℕ) :
    (∀ i, (increasingCochainTower M U i).X n) →ₗ[R] (Basic.singularCochains M X).X n :=
  (Coefficients.singularDegreewiseFunctionIso M X n).inv.hom.comp
    (LinearMap.pi fun s : Basic.singularSimplices X n =>
      (Coefficients.simplicialEvaluation _ M (increasingSimplexLift U hmono hcover s)).hom.comp
        (LinearMap.proj (increasingSimplexIndex U hmono hcover s)))

theorem increasingCochainGlue_evaluation (n : ℕ)
    (c : ∀ i, (increasingCochainTower M U i).X n) (s : Basic.singularSimplices X n) :
    Coefficients.simplicialEvaluation (TopCat.toSSet.obj X) M s (increasingCochainGlue M U hmono hcover n c) =
      Coefficients.simplicialEvaluation _ M (increasingSimplexLift U hmono hcover s)
        (c (increasingSimplexIndex U hmono hcover s)) := by
  rw [← Coefficients.degreewiseFunctionIso_hom_apply]
  change (Coefficients.singularDegreewiseFunctionIso M X n).hom
    ((Coefficients.singularDegreewiseFunctionIso M X n).inv _) s = _
  rw [Iso.inv_hom_id_apply]
  rfl

/-- Simultaneous restrictions of a global cochain to all cover members. -/
def increasingCochainRestrictions (n : ℕ) :
    (Basic.singularCochains M X).X n →ₗ[R] (∀ i, (increasingCochainTower M U i).X n) :=
  LinearMap.pi fun i => ((increasingCochainRestriction M U i).f n).hom

theorem increasingCochainGlue_restrictions (n : ℕ) (c : (Basic.singularCochains M X).X n) :
    increasingCochainGlue M U hmono hcover n (increasingCochainRestrictions M U n c) = c := by
  apply singularCochain_eq_of_evaluation_eq M n
  intro s
  rw [increasingCochainGlue_evaluation]
  exact (increasingCochainRestriction_evaluation M U
    (increasingSimplexIndex U hmono hcover s) n c (increasingSimplexLift U hmono hcover s)).trans
      (congrArg (fun t => Coefficients.simplicialEvaluation (TopCat.toSSet.obj X) M t c)
        (increasingSimplexLift_spec U hmono hcover s))

/-- Gluing a compatible family gives back each specified local cochain. -/
theorem increasingCochainRestrictions_glue (n : ℕ)
    (c : ∀ i, (increasingCochainTower M U i).X n)
    (hc : ∀ i, c i = (increasingCochainTransition M U hmono i).f n (c (i + 1))) :
    increasingCochainRestrictions M U n (increasingCochainGlue M U hmono hcover n c) = c := by
  funext i
  apply singularCochain_eq_of_evaluation_eq M n
  intro t
  calc
    _ = Coefficients.simplicialEvaluation (TopCat.toSSet.obj X) M
        ((TopCat.toSSet.map (U i).inclusion').app (op ⦋n⦌) t)
        (increasingCochainGlue M U hmono hcover n c) :=
      increasingCochainRestriction_evaluation M U i n _ t
    _ = _ := (increasingCochainGlue_evaluation M U hmono hcover n c _).trans
      (increasingCochain_evaluation_independent M U hmono n c hc
        (increasingSimplexLift U hmono hcover _) t
        (increasingSimplexLift_spec U hmono hcover _))

include hcover in
/-- The explicit degreewise universal property: every compatible local
family is the family of restrictions of a unique actual global cochain. -/
theorem existsUnique_increasingCochain (n : ℕ)
    (c : ∀ i, (increasingCochainTower M U i).X n)
    (hc : ∀ i, c i = (increasingCochainTransition M U hmono i).f n (c (i + 1))) :
    ∃! a : (Basic.singularCochains M X).X n,
      ∀ i, (increasingCochainRestriction M U i).f n a = c i := by
  refine ⟨increasingCochainGlue M U hmono hcover n c, ?_, ?_⟩
  · intro i
    exact congrFun (increasingCochainRestrictions_glue M U hmono hcover n c hc) i
  · intro a ha
    calc
      a = increasingCochainGlue M U hmono hcover n
          (increasingCochainRestrictions M U n a) :=
        (increasingCochainGlue_restrictions M U hmono hcover n a).symm
      _ = increasingCochainGlue M U hmono hcover n c :=
        congrArg (increasingCochainGlue M U hmono hcover n) (funext ha)

/-- Restrictions land in the actual compatible-sequence submodule of the
cochain tower. -/
def increasingCochainCompatibleMap (n : ℕ) :
    (Basic.singularCochains M X).X n →ₗ[R]
      Topology.Euclidean.Telescope.telescopeCompatible R (fun i => (increasingCochainTower M U i).X n)
        (fun i => ((increasingCochainTransition M U hmono i).f n).hom) :=
  LinearMap.codRestrict _ (increasingCochainRestrictions M U n) (by
    intro c i
    exact (congrArg (fun f : Basic.singularCochains M X ⟶ increasingCochainTower M U i =>
      f.f n c) (increasingCochainRestriction_pullback M U hmono (Nat.le_succ i))).symm)

/-- Genuine singular cochains identify linearly with compatible families
over the increasing open cover. -/
def increasingCochainEquiv (n : ℕ) :
    (Basic.singularCochains M X).X n ≃ₗ[R]
      Topology.Euclidean.Telescope.telescopeCompatible R (fun i => (increasingCochainTower M U i).X n)
        (fun i => ((increasingCochainTransition M U hmono i).f n).hom) where
  toLinearMap := increasingCochainCompatibleMap M U hmono n
  invFun c := increasingCochainGlue M U hmono hcover n c.val
  left_inv := increasingCochainGlue_restrictions M U hmono hcover n
  right_inv c := Subtype.ext
    (increasingCochainRestrictions_glue M U hmono hcover n c.val c.property)

@[simp]
theorem increasingCochainEquiv_apply (n : ℕ) (c : (Basic.singularCochains M X).X n) (i : ℕ) :
    (increasingCochainEquiv M U hmono hcover n c).val i =
      (increasingCochainRestriction M U i).f n c := rfl

/-- The compatible-family identification intertwines the actual singular
coboundary with the componentwise coboundaries of the cochain tower. -/
theorem increasingCochainEquiv_d (p q : ℕ) (c : (Basic.singularCochains M X).X p) (i : ℕ) :
    (increasingCochainEquiv M U hmono hcover q ((Basic.singularCochains M X).d p q c)).val i =
      (increasingCochainTower M U i).d p q
        ((increasingCochainEquiv M U hmono hcover p c).val i) :=
  (ConcreteCategory.congr_hom ((increasingCochainRestriction M U i).comm p q) c).symm

end

end OAI.AlgebraicTopology.Cohomology.Singular.IncreasingCochains
