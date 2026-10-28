import OAI.AlgebraicTopology.Cohomology.Singular.NormalizedCubicalTriangulation
import OAI.AlgebraicTopology.Cohomology.Singular.CubicalTriangulationBoundary
import OAI.AlgebraicTopology.Cohomology.Singular.SmoothComparison
import OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality
import OAI.AlgebraicTopology.DeRham.Comparison.CubicalLocalCochains
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero

/-! # Cubical Triangulation Comparison -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.CubicalTriangulationComparison

noncomputable section

/-!
# Euclidean comparison for normalized cubical triangulation

The positive-degree groups vanish by actual contractions. In degree zero,
the comparison preserves the ordinary augmentation, identifying the same
integer coefficient on both sides.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open OAI.AlgebraicTopology.DeRham.Comparison.CubicalLocalCochains
open scoped Simplicial BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [Ring R]

/-- A genuine homotopy equivalence of spaces induces a chain homotopy
equivalence on ordinary singular chains with module coefficients. -/
def continuousSingularChainHomotopyEquiv (M : ModuleCat.{0} R)
    {X Y : TopCat.{0}} (e : ContinuousMap.HomotopyEquiv X Y) :
    _root_.HomotopyEquiv ((TopCat.toSSet.obj X).chainComplex M)
      ((TopCat.toSSet.obj Y).chainComplex M) where
  hom := SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom e.toFun)) M
  inv := SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom e.invFun)) M
  homotopyHomInvId := by
    have H : TopCat.Homotopy
        (TopCat.ofHom e.toFun ≫ TopCat.ofHom e.invFun) (𝟙 X) := e.left_inv.some
    have Hs := H.toSSet (X := X) (Y := X)
    rw [TopCat.toSSet.map_comp, TopCat.toSSet.map_id] at Hs
    have Hc := Hs.chainComplexMap M
    dsimp only [SSet.chainComplexMap] at Hc ⊢
    rw [((SSet.chainComplexFunctor (ModuleCat.{0} R)).obj M).map_comp,
      ((SSet.chainComplexFunctor (ModuleCat.{0} R)).obj M).map_id] at Hc
    exact Hc
  homotopyInvHomId := by
    have H : TopCat.Homotopy
        (TopCat.ofHom e.invFun ≫ TopCat.ofHom e.toFun) (𝟙 Y) := e.right_inv.some
    have Hs := H.toSSet (X := Y) (Y := Y)
    rw [TopCat.toSSet.map_comp, TopCat.toSSet.map_id] at Hs
    have Hc := Hs.chainComplexMap M
    dsimp only [SSet.chainComplexMap] at Hc ⊢
    rw [((SSet.chainComplexFunctor (ModuleCat.{0} R)).obj M).map_comp,
      ((SSet.chainComplexFunctor (ModuleCat.{0} R)).obj M).map_id] at Hc
    exact Hc

/-- Positive ordinary singular homology vanishes on an actual contractible
space, by its homotopy equivalence with a point. -/
theorem isZero_continuousSingularHomology_of_contractible
    (M : ModuleCat.{0} R) (X : TopCat.{0}) [ContractibleSpace X]
    (n : ℕ) (hn : n ≠ 0) :
    IsZero (((TopCat.toSSet.obj X).chainComplex M).homology n) := by
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit X
  have h := AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    (ModuleCat.{0} R) n M (TopCat.of Unit) hn
  exact h.of_iso ((continuousSingularChainHomotopyEquiv M
    (Y := TopCat.of Unit) e).toHomologyIso n)

/-- The actual normalized smooth singular homology maps isomorphically to
ordinary singular homology on Euclidean space. -/
def normalizedSmoothHomologyComparisonIso (m n : ℕ) :
    (NormalizedCubicalTriangulation.normalizedSmoothIntegralChains m).homology n ≅
      (((TopCat.toSSet.obj (TopCat.of (Fin m → ℝ))).chainComplex
        (ModuleCat.of ℤ ℤ)).homology n) :=
  (((Smooth.smoothSingularSubcomplex (Fin m → ℝ)).toSSet.homotopyEquivNormalizedChainComplex
    (ModuleCat.of ℤ ℤ)).toHomologyIso n).symm ≪≫
      (SmoothComparison.smoothChainComparisonHomotopyEquiv (ModuleCat.of ℤ ℤ)
        (0 : Fin m → ℝ)).toHomologyIso n

/-- Positive normalized smooth singular homology vanishes on Euclidean space. -/
theorem isZero_normalizedSmoothHomology (m n : ℕ) (hn : n ≠ 0) :
    IsZero ((NormalizedCubicalTriangulation.normalizedSmoothIntegralChains m).homology n) :=
  (isZero_continuousSingularHomology_of_contractible (ModuleCat.of ℤ ℤ)
    (TopCat.of (Fin m → ℝ)) n hn).of_iso
      (normalizedSmoothHomologyComparisonIso m n)

/-- The degree-zero target comparison uses the ordinary, canonical singular
augmentation to the integer coefficients. -/
def normalizedSmoothHomologyZeroIso (m : ℕ) :
    (NormalizedCubicalTriangulation.normalizedSmoothIntegralChains m).homology 0 ≅ ModuleCat.of ℤ ℤ := by
  letI : PathConnectedSpace (TopCat.of (Fin m → ℝ)) :=
    inferInstanceAs (PathConnectedSpace (Fin m → ℝ))
  exact normalizedSmoothHomologyComparisonIso m 0 ≪≫
    asIso ((TopCat.of (Fin m → ℝ)).singularHomology₀ε (ModuleCat.of ℤ ℤ))

/-- A homology functional obtained from an opcycle functional evaluates on a
represented cycle by that original functional. -/
theorem chainClass_descOpcycles (C : ChainComplex (ModuleCat.{0} R) ℕ)
    (n j : ℕ) (hj : (ComplexShape.down ℕ).prev n = j)
    {M : ModuleCat.{0} R} (φ : C.X n ⟶ M) (hφ : C.d j n ≫ φ = 0)
    (z : ChainRepresentatives.chainCycles C n) :
    (C.homologyι n ≫ C.descOpcycles φ j hj hφ) (ChainRepresentatives.chainClass C n z) =
      φ (z : C.X n) := by
  rw [ChainRepresentatives.chainClass_eq_homologyπ]
  have h : C.homologyπ n ≫ C.homologyι n ≫ C.descOpcycles φ j hj hφ =
      C.iCycles n ≫ φ := by
    rw [← Category.assoc, HomologicalComplex.homology_π_ι, Category.assoc,
      HomologicalComplex.p_descOpcycles]
  have hi := ConcreteCategory.congr_hom ((C.sc n).moduleCatCyclesIso_inv_iCycles) z
  have hc := ConcreteCategory.congr_hom h ((C.sc n).moduleCatCyclesIso.inv z)
  change (C.iCycles n) ((C.sc n).moduleCatCyclesIso.inv z) = (z : C.X n) at hi
  simpa only [ModuleCat.comp_apply, hi] using hc

/-- The usual simplicial augmentation evaluates every degree-zero simplex
generator to its coefficient. -/
theorem chainClass_simplex_homologyZeroAugmentation (K : SSet.{0})
    (M : ModuleCat.{0} R) (s : K _⦋0⦌) (a : M) :
    (K.homology₀ε M) (ChainRepresentatives.chainClass (K.chainComplex M) 0
      ⟨K.ιChainComplex (R := M) s a, ChainRepresentatives.mem_chainCycles_zero _ _⟩) = a := by
  let C := K.chainComplex M
  let lift : M ⟶ C.cycles 0 :=
    C.liftCycles (K.ιChainComplex (R := M) s) 0 (by simp) (by simp)
  have hcycle : (C.sc 0).moduleCatCyclesIso.inv
      ⟨K.ιChainComplex (R := M) s a, ChainRepresentatives.mem_chainCycles_zero C _⟩ = lift a := by
    apply (ModuleCat.mono_iff_injective (C.iCycles 0)).mp inferInstance
    have hleft := ConcreteCategory.congr_hom ((C.sc 0).moduleCatCyclesIso_inv_iCycles)
      ⟨K.ιChainComplex (R := M) s a, ChainRepresentatives.mem_chainCycles_zero C _⟩
    have hright := ConcreteCategory.congr_hom
      (C.liftCycles_i (K.ιChainComplex (R := M) s) 0 (by simp) (by simp)) a
    exact hleft.trans hright.symm
  rw [ChainRepresentatives.chainClass_eq_homologyπ, hcycle]
  exact ConcreteCategory.congr_hom
    (K.liftCycles_ιChainComplex_homologyπ_homology₀ε M s) a

/-- The target degree-zero isomorphism sends each actual normalized smooth
simplex generator to its coefficient. -/
theorem normalizedSmoothHomologyZeroIso_simplex (m : ℕ)
    (s : (Smooth.smoothSingularSubcomplex (Fin m → ℝ)).toSSet _⦋0⦌) (a : ℤ) :
    (normalizedSmoothHomologyZeroIso m).hom
      (ChainRepresentatives.chainClass (NormalizedCubicalTriangulation.normalizedSmoothIntegralChains m) 0
        ⟨(Smooth.smoothSingularSubcomplex (Fin m → ℝ)).toSSet.ιNormalizedChainComplex
          (R := ModuleCat.of ℤ ℤ) s a, ChainRepresentatives.mem_chainCycles_zero _ _⟩) = a := by
  let K := (Smooth.smoothSingularSubcomplex (Fin m → ℝ)).toSSet
  let A := ModuleCat.of ℤ ℤ
  let e := (K.homotopyEquivNormalizedChainComplex A).toHomologyIso 0
  have hn : e.hom (ChainRepresentatives.chainClass (K.chainComplex A) 0
      ⟨K.ιChainComplex (R := A) s a, ChainRepresentatives.mem_chainCycles_zero _ _⟩) =
      ChainRepresentatives.chainClass (K.normalizedChainComplex A) 0
        ⟨K.ιNormalizedChainComplex (R := A) s a, ChainRepresentatives.mem_chainCycles_zero _ _⟩ := by
    change HomologicalComplex.homologyMap (K.toNormalizedChainComplex A) 0 _ = _
    rw [EvaluationNaturality.chainClass_naturality]
    rfl
  rw [← hn]
  change (TopCat.toSSet.obj (TopCat.of (Fin m → ℝ))).homology₀ε A
    (HomologicalComplex.homologyMap (Smooth.smoothSingularChainInclusion A (Fin m → ℝ)) 0
      (e.inv (e.hom (ChainRepresentatives.chainClass (K.chainComplex A) 0
        ⟨K.ιChainComplex (R := A) s a, ChainRepresentatives.mem_chainCycles_zero _ _⟩)))) = a
  rw [ModuleCat.inv_hom_apply, EvaluationNaturality.chainClass_naturality]
  have hi : EvaluationNaturality.chainCycleMap (Smooth.smoothSingularChainInclusion A (Fin m → ℝ)) 0
      ⟨K.ιChainComplex (R := A) s a, ChainRepresentatives.mem_chainCycles_zero _ _⟩ =
      ⟨(TopCat.toSSet.obj (TopCat.of (Fin m → ℝ))).ιChainComplex (R := A) s.val a,
        ChainRepresentatives.mem_chainCycles_zero _ _⟩ := by
    apply Subtype.ext
    exact ConcreteCategory.congr_hom
      (SSet.ι_chainComplexMap_f (X := K)
        (Y := TopCat.toSSet.obj (TopCat.of (Fin m → ℝ))) (R := A)
        (Smooth.smoothSingularInclusion (Fin m → ℝ)) s) a
  rw [hi]
  exact chainClass_simplex_homologyZeroAugmentation _ A s.val a

/-- In degree zero the signed triangulation consists of the single actual
simplex corresponding to the unique empty permutation. -/
theorem normalizedCubeTriangulation_zero {m : ℕ}
    (cube : DeRham.Comparison.StokesF.SingularCubeStokes.SmoothSingularCube 0 m) :
    NormalizedCubicalTriangulation.normalizedCubeTriangulation cube =
      (Smooth.smoothSingularSubcomplex (Fin m → ℝ)).toSSet.ιNormalizedChainComplex
        (R := ModuleCat.of ℤ ℤ)
        (CubicalTriangulation.triangulatedCubeSmoothSimplex cube (Equiv.refl (Fin 0))) 1 := by
  classical
  unfold NormalizedCubicalTriangulation.normalizedCubeTriangulation
  rw [Fintype.sum_unique]
  have he : (default : Equiv.Perm (Fin 0)) = Equiv.refl (Fin 0) := Subsingleton.elim _ _
  rw [he]
  simp

/-- Every zero-chain in a nonnegative chain complex defines a homology class. -/
def zeroChainClass (C : ChainComplex (ModuleCat.{0} R) ℕ) :
    C.X 0 →ₗ[R] C.homology 0 :=
  (ChainRepresentatives.chainClass C 0).comp
    ((LinearMap.id : C.X 0 →ₗ[R] C.X 0).codRestrict (ChainRepresentatives.chainCycles C 0)
      (ChainRepresentatives.mem_chainCycles_zero C))

@[simp]
theorem zeroChainClass_apply (C : ChainComplex (ModuleCat.{0} R) ℕ) (c : C.X 0) :
    zeroChainClass C c = ChainRepresentatives.chainClass C 0 ⟨c, ChainRepresentatives.mem_chainCycles_zero C c⟩ := rfl

/-- The zero-chain class map is surjective onto the actual homology object. -/
theorem zeroChainClass_surjective (C : ChainComplex (ModuleCat.{0} R) ℕ) :
    Function.Surjective (zeroChainClass C) := by
  intro h
  obtain ⟨z, rfl⟩ := ChainRepresentatives.chainClass_surjective C 0 h
  exact ⟨z.val, rfl⟩

/-- The canonical target augmentation, evaluated on actual zero-chains. -/
def normalizedSmoothZeroAugmentation (m : ℕ) :
    (NormalizedCubicalTriangulation.normalizedSmoothIntegralChains m).X 0 →ₗ[ℤ] ℤ :=
  (normalizedSmoothHomologyZeroIso m).hom.hom.comp
    (zeroChainClass (NormalizedCubicalTriangulation.normalizedSmoothIntegralChains m))

@[simp]
theorem normalizedSmoothZeroAugmentation_simplex (m : ℕ)
    (s : (Smooth.smoothSingularSubcomplex (Fin m → ℝ)).toSSet _⦋0⦌) (a : ℤ) :
    normalizedSmoothZeroAugmentation m
      ((Smooth.smoothSingularSubcomplex (Fin m → ℝ)).toSSet.ιNormalizedChainComplex
        (R := ModuleCat.of ℤ ℤ) s a) = a :=
  normalizedSmoothHomologyZeroIso_simplex m s a

/-- Degree-zero cube triangulation preserves the generator's coefficient. -/
theorem normalizedSmoothZeroAugmentation_cube {m : ℕ}
    (cube : DeRham.Comparison.StokesF.SingularCubeStokes.SmoothSingularCube 0 m) :
    normalizedSmoothZeroAugmentation m (NormalizedCubicalTriangulation.normalizedCubeTriangulation cube) = 1 := by
  rw [normalizedCubeTriangulation_zero]
  exact normalizedSmoothZeroAugmentation_simplex m _ 1

/-- The actual normalized triangulation preserves the coefficient-sum
augmentation on every zero-chain, including after quotient descent. -/
theorem normalizedCubicalTriangulation_augmentation {m : ℕ}
    (c : DeRham.Comparison.CubicalDegenerateQ.NormalizedCubicalChain 0 m) :
    normalizedSmoothZeroAugmentation m (NormalizedCubicalTriangulation.normalizedCubicalTriangulation 0 m c) =
      DeRham.Comparison.CubicalLocalCochains.normalizedCubicalAugmentation m c := by
  refine Submodule.Quotient.induction_on (DeRham.Comparison.CubicalDegenerateQ.degenerateSubmodule 0 m) c ?_
  intro d
  change normalizedSmoothZeroAugmentation m (NormalizedCubicalTriangulation.cubicalToNormalizedSimplicialLinear 0 m d) =
    Finsupp.degree d
  induction d using Finsupp.induction with
  | zero => simp only [map_zero]
  | single_add cube a d hcube ha ih =>
    rw [map_add, map_add, map_add, ih, NormalizedCubicalTriangulation.cubicalToNormalizedSimplicialLinear_single,
      map_zsmul, normalizedSmoothZeroAugmentation_cube, Finsupp.degree_single]
    simp only [zsmul_eq_mul, mul_one, Int.cast_id]

/-- Every positive-degree normalized Euclidean cubical homology group is zero. -/
theorem isZero_normalizedCubicalHomology_succ (m n : ℕ) :
    IsZero ((CubicalTriangulationBoundary.normalizedCubicalChainComplex m).homology (n + 1)) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  have hz : ∀ z : (CubicalTriangulationBoundary.normalizedCubicalChainComplex m).homology (n + 1), z = 0 := by
    intro z
    obtain ⟨c, rfl⟩ := ChainRepresentatives.chainClass_surjective (CubicalTriangulationBoundary.normalizedCubicalChainComplex m) (n + 1) z
    apply (ChainRepresentatives.chainClass_eq_zero_iff_exists (CubicalTriangulationBoundary.normalizedCubicalChainComplex m) (n + 1) c).mpr
    have hc : DeRham.Comparison.CubicalDegenerateQ.normalizedBoundary n m c.val = 0 := by
      have h := (ChainRepresentatives.mem_chainCycles_iff_succ (CubicalTriangulationBoundary.normalizedCubicalChainComplex m) n c.val).mp
        c.property
      rw [CubicalTriangulationBoundary.normalizedCubicalChainComplex_d] at h
      change DeRham.Comparison.CubicalDegenerateQ.normalizedBoundary n m c.val = 0 at h
      exact h
    refine ⟨DeRham.Comparison.CubicalPrism.normalizedPrism (n + 1) m (0 : Fin m → ℝ) c.val, ?_⟩
    rw [CubicalTriangulationBoundary.normalizedCubicalChainComplex_d]
    exact DeRham.Comparison.CubicalPrism.normalized_cycle_is_boundary (0 : Fin m → ℝ) c.val hc
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

/-- The cubical augmentation annihilates the differential of the packaged
normalized chain complex. -/
theorem normalizedCubicalAugmentation_d (m : ℕ) :
    (CubicalTriangulationBoundary.normalizedCubicalChainComplex m).d 1 0 ≫
      ModuleCat.ofHom (DeRham.Comparison.CubicalLocalCochains.normalizedCubicalAugmentation m) = 0 := by
  rw [CubicalTriangulationBoundary.normalizedCubicalChainComplex_d]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  exact DeRham.Comparison.CubicalLocalCochains.normalizedCubicalAugmentation_boundary

/-- The actual cubical coefficient-sum augmentation descends to zeroth homology. -/
def normalizedCubicalHomologyZeroAugmentation (m : ℕ) :
    (CubicalTriangulationBoundary.normalizedCubicalChainComplex m).homology 0 ⟶ ModuleCat.of ℤ ℤ :=
  (CubicalTriangulationBoundary.normalizedCubicalChainComplex m).homologyι 0 ≫
    (CubicalTriangulationBoundary.normalizedCubicalChainComplex m).descOpcycles
      (ModuleCat.ofHom (DeRham.Comparison.CubicalLocalCochains.normalizedCubicalAugmentation m)) 1 (by simp)
      (normalizedCubicalAugmentation_d m)

/-- The cubical prism makes the degree-zero augmentation an isomorphism. -/
theorem isIso_normalizedCubicalHomologyZeroAugmentation (m : ℕ) :
    IsIso (normalizedCubicalHomologyZeroAugmentation m) := by
  have he : (ShortComplex.mk
      ((CubicalTriangulationBoundary.normalizedCubicalChainComplex m).d 1 0)
      (ModuleCat.ofHom (DeRham.Comparison.CubicalLocalCochains.normalizedCubicalAugmentation m))
      (normalizedCubicalAugmentation_d m)).Exact := by
    apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro c hc
    refine ⟨DeRham.Comparison.CubicalPrism.normalizedPrism 0 m (0 : Fin m → ℝ) c, ?_⟩
    change (CubicalTriangulationBoundary.normalizedCubicalChainComplex m).d 1 0
      (DeRham.Comparison.CubicalPrism.normalizedPrism 0 m (0 : Fin m → ℝ) c) = c
    rw [CubicalTriangulationBoundary.normalizedCubicalChainComplex_d]
    exact DeRham.Comparison.CubicalLocalCochains.normalized_aug_zero_is_boundary (0 : Fin m → ℝ) c hc
  have hep : Epi (ModuleCat.ofHom (DeRham.Comparison.CubicalLocalCochains.normalizedCubicalAugmentation m)) :=
    (ModuleCat.epi_iff_surjective _).mpr
      (DeRham.Comparison.CubicalLocalCochains.normalizedCubicalAugmentation_surjective (0 : Fin m → ℝ))
  have : IsIso ((CubicalTriangulationBoundary.normalizedCubicalChainComplex m).descOpcycles
      (ModuleCat.ofHom (DeRham.Comparison.CubicalLocalCochains.normalizedCubicalAugmentation m)) 1 (by simp)
      (normalizedCubicalAugmentation_d m)) :=
    (ChainComplex.isIso_descOpcycles_iff _ _ (normalizedCubicalAugmentation_d m)).mpr
      ⟨he, hep⟩
  dsimp only [normalizedCubicalHomologyZeroAugmentation]
  infer_instance

/-- Zeroth normalized Euclidean cubical homology is the integer coefficients,
via the actual coefficient-sum augmentation. -/
def normalizedCubicalHomologyZeroIso (m : ℕ) :
    (CubicalTriangulationBoundary.normalizedCubicalChainComplex m).homology 0 ≅ ModuleCat.of ℤ ℤ := by
  letI := isIso_normalizedCubicalHomologyZeroAugmentation m
  exact asIso (normalizedCubicalHomologyZeroAugmentation m)

@[simp]
theorem normalizedCubicalHomologyZeroIso_zeroChainClass {m : ℕ}
    (c : DeRham.Comparison.CubicalDegenerateQ.NormalizedCubicalChain 0 m) :
    (normalizedCubicalHomologyZeroIso m).hom
      (zeroChainClass (CubicalTriangulationBoundary.normalizedCubicalChainComplex m) c) =
        DeRham.Comparison.CubicalLocalCochains.normalizedCubicalAugmentation m c :=
  chainClass_descOpcycles (CubicalTriangulationBoundary.normalizedCubicalChainComplex m) 0 1 (by simp)
    (ModuleCat.ofHom (DeRham.Comparison.CubicalLocalCochains.normalizedCubicalAugmentation m))
    (normalizedCubicalAugmentation_d m) ⟨c, ChainRepresentatives.mem_chainCycles_zero _ _⟩

/-- The inverse sends an integer to that multiple of any chosen point class. -/
theorem normalizedCubicalHomologyZeroIso_inv (m : ℕ) (x : Fin m → ℝ) (a : ℤ) :
    (normalizedCubicalHomologyZeroIso m).inv a =
      zeroChainClass (CubicalTriangulationBoundary.normalizedCubicalChainComplex m) (a • DeRham.Comparison.CubicalLocalCochains.normalizedPointChain x) := by
  apply (ModuleCat.mono_iff_injective (normalizedCubicalHomologyZeroIso m).hom).mp
    inferInstance
  rw [ModuleCat.hom_inv_apply, normalizedCubicalHomologyZeroIso_zeroChainClass]
  simp only [map_smul, DeRham.Comparison.CubicalLocalCochains.normalizedCubicalAugmentation_point, smul_eq_mul, mul_one]

/-- Degree-zero class maps commute with actual chain maps. -/
theorem zeroChainClass_naturality
    {C D : ChainComplex (ModuleCat.{0} ℤ) ℕ} (f : C ⟶ D) (c : C.X 0) :
    (HomologicalComplex.homologyMap f 0) (zeroChainClass C c) =
      zeroChainClass D ((f.f 0) c) :=
  EvaluationNaturality.chainClass_naturality f 0 ⟨c, ChainRepresentatives.mem_chainCycles_zero C c⟩

/-- The actual triangulation identifies the same zeroth homology coefficient
on the cubical and smooth simplicial sides. -/
theorem normalizedCubicalTriangulation_homologyZero_augmentation (m : ℕ) :
    HomologicalComplex.homologyMap (CubicalTriangulationBoundary.normalizedCubicalTriangulationChainMap m) 0 ≫
      (normalizedSmoothHomologyZeroIso m).hom =
        (normalizedCubicalHomologyZeroIso m).hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  obtain ⟨c, rfl⟩ := zeroChainClass_surjective (CubicalTriangulationBoundary.normalizedCubicalChainComplex m) z
  change (normalizedSmoothHomologyZeroIso m).hom
    ((HomologicalComplex.homologyMap (CubicalTriangulationBoundary.normalizedCubicalTriangulationChainMap m) 0)
      (zeroChainClass (CubicalTriangulationBoundary.normalizedCubicalChainComplex m) c)) = _
  rw [zeroChainClass_naturality, normalizedCubicalHomologyZeroIso_zeroChainClass]
  exact normalizedCubicalTriangulation_augmentation c

/-- The degree-zero homology map of the actual triangulation is an isomorphism. -/
theorem isIso_normalizedCubicalTriangulation_homologyZero (m : ℕ) :
    IsIso (HomologicalComplex.homologyMap (CubicalTriangulationBoundary.normalizedCubicalTriangulationChainMap m) 0) := by
  have : IsIso (HomologicalComplex.homologyMap
      (CubicalTriangulationBoundary.normalizedCubicalTriangulationChainMap m) 0 ≫
        (normalizedSmoothHomologyZeroIso m).hom) := by
    rw [normalizedCubicalTriangulation_homologyZero_augmentation]
    infer_instance
  exact IsIso.of_isIso_comp_right
    (HomologicalComplex.homologyMap (CubicalTriangulationBoundary.normalizedCubicalTriangulationChainMap m) 0)
    (normalizedSmoothHomologyZeroIso m).hom

/-- Signed normalized cubical triangulation is a quasi-isomorphism on every
Euclidean target. Both complexes and the connecting map are the actual
constructed chain complexes and actual permutation-simplex triangulation. -/
theorem quasiIso_normalizedCubicalTriangulation (m : ℕ) :
    QuasiIso (CubicalTriangulationBoundary.normalizedCubicalTriangulationChainMap m) := by
  rw [quasiIso_iff]
  intro n
  cases n with
  | zero =>
    exact (quasiIsoAt_iff_isIso_homologyMap _ 0).mpr
      (isIso_normalizedCubicalTriangulation_homologyZero m)
  | succ n =>
    apply (quasiIsoAt_iff_exactAt _ (n + 1)
      ((HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
        (isZero_normalizedCubicalHomology_succ m n))).mpr
    exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
      (isZero_normalizedSmoothHomology m (n + 1) (Nat.succ_ne_zero n))

/-- The homology isomorphism induced by the actual normalized triangulation
in every degree. -/
def normalizedCubicalTriangulationHomologyIso (m n : ℕ) :
    (CubicalTriangulationBoundary.normalizedCubicalChainComplex m).homology n ≅
      (NormalizedCubicalTriangulation.normalizedSmoothIntegralChains m).homology n := by
  letI := quasiIso_normalizedCubicalTriangulation m
  exact asIso (HomologicalComplex.homologyMap (CubicalTriangulationBoundary.normalizedCubicalTriangulationChainMap m) n)

/-- The forward isomorphism is precisely the homology map of the signed
permutation-simplex triangulation. -/
@[simp]
theorem normalizedCubicalTriangulationHomologyIso_hom (m n : ℕ) :
    (normalizedCubicalTriangulationHomologyIso m n).hom =
      HomologicalComplex.homologyMap (CubicalTriangulationBoundary.normalizedCubicalTriangulationChainMap m) n := rfl

end

end OAI.AlgebraicTopology.Cohomology.Singular.CubicalTriangulationComparison
