import OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.Homotopy

/-! # Eventually Small -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.EventuallySmall.Cycles

noncomputable section

/-!
# An eventual-subdivision criterion for a genuine chain inclusion

Let an injective chain map identify a chain complex with a subcomplex of
another one. Suppose compatible endomorphisms of both complexes are each
chain homotopic to the identity, and every ambient chain eventually enters
the subcomplex under iteration. Then the inclusion is a quasi-isomorphism.

All maps and homotopies in this theorem are actual mathlib chain maps and
homotopies. The theorem does not assume or assert that any unconstructed
geometric subdivision operator satisfies these hypotheses.
-/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality

variable {R : Type} [CommRing R]
variable {C D : ChainComplex (ModuleCat.{0} R) ℕ}

/-- Iteration of an actual chain endomorphism. -/
def iterateChainMap (s : C ⟶ C) : ℕ → (C ⟶ C)
  | 0 => 𝟙 C
  | N + 1 => iterateChainMap s N ≫ s

@[simp]
theorem iterateChainMap_apply (s : C ⟶ C) (N n : ℕ) (x : C.X n) :
    ((Cycles.iterateChainMap s N).f n) x = ((s.f n)^[N]) x := by
  induction N with
  | zero => rfl
  | succ N ih =>
    change (s.f n) (((Cycles.iterateChainMap s N).f n) x) = ((s.f n)^[N + 1]) x
    rw [ih, Function.iterate_succ_apply']

/-- A compatible chain inclusion commutes with all iterates. -/
theorem iterateChainMap_commute (i : C ⟶ D) (sC : C ⟶ C) (sD : D ⟶ D)
    (h : i ≫ sD = sC ≫ i) (N : ℕ) :
    i ≫ Cycles.iterateChainMap sD N = Cycles.iterateChainMap sC N ≫ i := by
  induction N with
  | zero => simp [Cycles.iterateChainMap]
  | succ N ih =>
    calc
      i ≫ Cycles.iterateChainMap sD (N + 1) = (i ≫ Cycles.iterateChainMap sD N) ≫ sD := by
        simp only [Cycles.iterateChainMap, Category.assoc]
      _ = (Cycles.iterateChainMap sC N ≫ i) ≫ sD := by rw [ih]
      _ = Cycles.iterateChainMap sC N ≫ (i ≫ sD) := Category.assoc _ _ _
      _ = Cycles.iterateChainMap sC N ≫ (sC ≫ i) := by rw [h]
      _ = Cycles.iterateChainMap sC (N + 1) ≫ i := by
        simp only [Cycles.iterateChainMap, Category.assoc]

/-- Iterating an endomorphism homotopic to the identity still acts as the
identity on genuine homology. -/
theorem iterateChainMap_homologyMap (s : C ⟶ C) (h : _root_.Homotopy s (𝟙 C))
    (N n : ℕ) :
    HomologicalComplex.homologyMap (Cycles.iterateChainMap s N) n = 𝟙 (C.homology n) := by
  have hs : HomologicalComplex.homologyMap s n = 𝟙 (C.homology n) := by
    simpa using h.homologyMap_eq n
  induction N with
  | zero => simp [Cycles.iterateChainMap]
  | succ N ih =>
    simp only [Cycles.iterateChainMap, HomologicalComplex.homologyMap_comp, ih, hs,
      Category.id_comp]

/-- A represented cycle retains its class under every iterate. -/
theorem iterateChainMap_class (s : C ⟶ C) (h : _root_.Homotopy s (𝟙 C))
    (N n : ℕ) (z : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles C n) :
    AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass C n (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (Cycles.iterateChainMap s N) n z) = AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass C n z := by
  rw [← AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainClass_naturality, iterateChainMap_homologyMap s h N n]
  rfl

/-- Injectivity of a chain inclusion lets one recognize a cycle in the
subcomplex from its image in the ambient complex. -/
theorem chainMap_preimage_isCycle (i : C ⟶ D)
    (hi : ∀ n, Function.Injective (i.f n)) (n : ℕ) (x : C.X n)
    (hx : (i.f n) x ∈ AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles D n) : x ∈ AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles C n := by
  change (D.d n ((ComplexShape.down ℕ).next n)) ((i.f n) x) = 0 at hx
  change (C.d n ((ComplexShape.down ℕ).next n)) x = 0
  apply hi ((ComplexShape.down ℕ).next n)
  simpa only [map_zero, ConcreteCategory.comp_apply] using
    (ConcreteCategory.congr_hom (i.comm n ((ComplexShape.down ℕ).next n)) x).symm.trans hx

/-- Moving a representative cycle into the subcomplex proves surjectivity on
homology. -/
theorem eventuallySmall_homology_surjective (i : C ⟶ D)
    (hi : ∀ n, Function.Injective (i.f n)) (sD : D ⟶ D)
    (hD : _root_.Homotopy sD (𝟙 D))
    (hevent : ∀ (n : ℕ) (x : D.X n),
      ∃ (N : ℕ) (y : C.X n), (i.f n) y = ((sD.f n)^[N]) x)
    (n : ℕ) : Function.Surjective (HomologicalComplex.homologyMap i n) := by
  intro y
  obtain ⟨z, rfl⟩ := AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_surjective D n y
  obtain ⟨N, x, hx⟩ := hevent n (z : D.X n)
  have hx' : (i.f n) x = ((Cycles.iterateChainMap sD N).f n) (z : D.X n) := by
    rw [iterateChainMap_apply]
    exact hx
  have hxc : x ∈ AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles C n := chainMap_preimage_isCycle i hi n x (by
    rw [hx']
    exact (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (Cycles.iterateChainMap sD N) n z).property)
  refine ⟨AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass C n ⟨x, hxc⟩, ?_⟩
  rw [AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainClass_naturality]
  have heq : AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap i n ⟨x, hxc⟩ = AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (Cycles.iterateChainMap sD N) n z :=
    Subtype.ext hx'
  rw [heq]
  exact iterateChainMap_class sD hD N n z

/-- Moving an ambient bounding chain into the subcomplex, and using the
restricted homotopy, proves injectivity on homology. -/
theorem eventuallySmall_homology_injective (i : C ⟶ D)
    (hi : ∀ n, Function.Injective (i.f n)) (sC : C ⟶ C) (sD : D ⟶ D)
    (hcomm : i ≫ sD = sC ≫ i) (hC : _root_.Homotopy sC (𝟙 C))
    (hevent : ∀ (n : ℕ) (x : D.X n),
      ∃ (N : ℕ) (y : C.X n), (i.f n) y = ((sD.f n)^[N]) x)
    (n : ℕ) : Function.Injective (HomologicalComplex.homologyMap i n) := by
  change Function.Injective (HomologicalComplex.homologyMap i n).hom
  apply (injective_iff_map_eq_zero (HomologicalComplex.homologyMap i n).hom).mpr
  intro y hy
  obtain ⟨z, rfl⟩ := AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_surjective C n y
  change (HomologicalComplex.homologyMap i n) (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass C n z) = 0 at hy
  rw [AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainClass_naturality] at hy
  obtain ⟨b, hb⟩ := (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_eq_zero_iff_exists D n (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap i n z)).mp hy
  change (D.d (n + 1) n) b = (i.f n) (z : C.X n) at hb
  obtain ⟨N, w, hw⟩ := hevent (n + 1) b
  have hw' : (i.f (n + 1)) w = ((Cycles.iterateChainMap sD N).f (n + 1)) b := by
    rw [iterateChainMap_apply]
    exact hw
  have hc := congrArg (fun f : C ⟶ D => (f.f n) (z : C.X n))
    (iterateChainMap_commute i sC sD hcomm N)
  change ((Cycles.iterateChainMap sD N).f n) ((i.f n) (z : C.X n)) =
    (i.f n) (((Cycles.iterateChainMap sC N).f n) (z : C.X n)) at hc
  have hbound : (C.d (n + 1) n) w =
      ((Cycles.iterateChainMap sC N).f n) (z : C.X n) := by
    apply hi n
    calc
      (i.f n) ((C.d (n + 1) n) w) = (D.d (n + 1) n) ((i.f (n + 1)) w) :=
        by simpa only [ConcreteCategory.comp_apply] using
          (ConcreteCategory.congr_hom (i.comm (n + 1) n) w).symm
      _ = (D.d (n + 1) n) (((Cycles.iterateChainMap sD N).f (n + 1)) b) := by rw [hw']
      _ = ((Cycles.iterateChainMap sD N).f n) ((D.d (n + 1) n) b) :=
        by simpa only [ConcreteCategory.comp_apply] using
          ConcreteCategory.congr_hom ((Cycles.iterateChainMap sD N).comm (n + 1) n) b
      _ = ((Cycles.iterateChainMap sD N).f n) ((i.f n) (z : C.X n)) := by rw [hb]
      _ = (i.f n) (((Cycles.iterateChainMap sC N).f n) (z : C.X n)) := hc
  have hzN : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass C n (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (Cycles.iterateChainMap sC N) n z) = 0 :=
    (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_eq_zero_iff_exists C n _).mpr ⟨w, hbound⟩
  rw [iterateChainMap_class sC hC N n z] at hzN
  exact hzN

/-- A genuine chain inclusion is a quasi-isomorphism when compatible
endomorphisms, chain homotopic to the identity on both complexes, eventually
move every ambient chain into its image. -/
theorem quasiIso_of_eventuallySmall (i : C ⟶ D)
    (hi : ∀ n, Function.Injective (i.f n)) (sC : C ⟶ C) (sD : D ⟶ D)
    (hcomm : i ≫ sD = sC ≫ i)
    (hC : _root_.Homotopy sC (𝟙 C)) (hD : _root_.Homotopy sD (𝟙 D))
    (hevent : ∀ (n : ℕ) (x : D.X n),
      ∃ (N : ℕ) (y : C.X n), (i.f n) y = ((sD.f n)^[N]) x) :
    _root_.QuasiIso i := by
  apply (quasiIso_iff i).mpr
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap,
    ConcreteCategory.isIso_iff_bijective]
  exact ⟨eventuallySmall_homology_injective i hi sC sD hcomm hC hevent n,
    eventuallySmall_homology_surjective i hi sD hD hevent n⟩

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.EventuallySmall.Cycles
