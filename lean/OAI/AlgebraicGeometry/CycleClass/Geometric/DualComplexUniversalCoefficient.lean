import OAI.AlgebraicTopology.Cohomology.Singular.UniversalCoefficient

/-! # Dual Complex Universal Coefficient -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.DualComplexUniversalCoefficient.Cycles

noncomputable section

/-!
# Evaluation duality for the actual dual of any chain complex

The cochain complex here has the genuine linear Hom spaces as its objects and
precomposition by the given chain differential as its differential. Its
cohomology evaluates on the given complex's categorical homology. Over a field,
extension of linear functionals proves that this canonical evaluation is an
isomorphism, in every degree including zero.
-/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Cohomology.Singular.UniversalCoefficient

section Complex

variable {R : Type} [CommRing R]

/-- The actual linear Hom cochain complex of a chain complex into a coefficient module. -/
def linearHomCochainComplex (C : ChainComplex (ModuleCat.{0} R) ℕ)
    (M : ModuleCat.{0} R) : CochainComplex (ModuleCat.{0} R) ℕ where
  X n := ModuleCat.of R (C.X n →ₗ[R] M)
  d i j := ModuleCat.ofHom
    { toFun := fun φ => φ.comp (C.d j i).hom
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  shape i j hij := by
    ext φ z
    change φ ((C.d j i) z) = 0
    rw [C.shape j i hij]
    exact map_zero φ
  d_comp_d' i j k _ _ := by
    ext φ z
    change φ ((C.d j i) ((C.d k j) z)) = 0
    have hz := ConcreteCategory.congr_hom (C.d_comp_d k j i) z
    change (C.d j i) ((C.d k j) z) = 0 at hz
    rw [hz, map_zero]

/-- The differential is precomposition by the actual chain differential, for all indices. -/
@[simp]
theorem linearHomCochainComplex_d_apply (C : ChainComplex (ModuleCat.{0} R) ℕ)
    (M : ModuleCat.{0} R) (i j : ℕ) (φ : C.X i →ₗ[R] M) :
    (linearHomCochainComplex C M).d i j φ = φ.comp (C.d j i).hom := rfl

/-- Precomposition by a chain map acts contravariantly on the actual Hom cochain complexes. -/
def linearHomCochainMap {C D : ChainComplex (ModuleCat.{0} R) ℕ}
    (f : C ⟶ D) (M : ModuleCat.{0} R) :
    linearHomCochainComplex D M ⟶ linearHomCochainComplex C M where
  f n := ModuleCat.ofHom
    { toFun := fun φ => φ.comp (f.f n).hom
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  comm' i j _ := by
    ext φ
    change (D.X i →ₗ[R] M) at φ
    apply LinearMap.ext
    intro z
    change φ ((f.f i) ((C.d j i) z)) = φ ((D.d j i) ((f.f j) z))
    exact congrArg φ (ConcreteCategory.congr_hom (f.comm j i) z).symm

@[simp]
theorem linearHomCochainMap_apply {C D : ChainComplex (ModuleCat.{0} R) ℕ}
    (f : C ⟶ D) (M : ModuleCat.{0} R) (n : ℕ) (φ : D.X n →ₗ[R] M) :
    (linearHomCochainMap f M).f n φ = φ.comp (f.f n).hom := rfl

/-- The scalar-valued linear dual cochain complex. -/
abbrev dualCochainComplex (C : ChainComplex (ModuleCat.{0} R) ℕ) :
    CochainComplex (ModuleCat.{0} R) ℕ := linearHomCochainComplex C (ModuleCat.of R R)

end Complex

section Evaluation

variable {R : Type} [CommRing R]

/-- A cocycle in the actual Hom complex vanishes on every chain boundary. -/
theorem linearHomCocycle_boundary (C : ChainComplex (ModuleCat.{0} R) ℕ)
    (M : ModuleCat.{0} R) (n i : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (linearHomCochainComplex C M) n) (z : C.X i) :
    DFunLike.coe (F := C.X n →ₗ[R] M) c.val ((C.d i n) z) = 0 := by
  have hc := AlgebraicTopology.Cohomology.Singular.Evaluation.cochainCocycle_d_eq_zero (linearHomCochainComplex C M) n i c
  change (c.val : C.X n →ₗ[R] M).comp (C.d i n).hom = 0 at hc
  exact LinearMap.congr_fun hc z

/-- A coboundary in the actual Hom complex vanishes on every chain cycle. -/
theorem linearHomCoboundary_cycle (C : ChainComplex (ModuleCat.{0} R) ℕ)
    (M : ModuleCat.{0} R) (i n : ℕ) (c : C.X i →ₗ[R] M)
    (z : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles C n) :
    DFunLike.coe (F := C.X n →ₗ[R] M) ((linearHomCochainComplex C M).d i n c) z.val = 0 := by
  change c ((C.d n i) z.val) = 0
  rw [AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycle_d_eq_zero C n i z, map_zero]

/-- A Hom-complex cocycle evaluates on the categorical homology of its chain complex. -/
def evaluateLinearHomCocycle (C : ChainComplex (ModuleCat.{0} R) ℕ)
    (M : ModuleCat.{0} R) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (linearHomCochainComplex C M) n) :
    C.homology n →ₗ[R] M :=
  ((AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainBoundaries C n).liftQ
    ((c.val : C.X n →ₗ[R] M).comp (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles C n).subtype)
    (by
      intro z hz
      rcases hz with ⟨w, rfl⟩
      change DFunLike.coe (F := C.X n →ₗ[R] M) c.val ((C.sc n).f w) = 0
      exact linearHomCocycle_boundary C M n _ c w)).comp
    (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.homologyQuotientIso C n).toLinearEquiv.toLinearMap

@[simp]
theorem evaluateLinearHomCocycle_chainClass (C : ChainComplex (ModuleCat.{0} R) ℕ)
    (M : ModuleCat.{0} R) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (linearHomCochainComplex C M) n) (z : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles C n) :
    evaluateLinearHomCocycle C M n c (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass C n z) =
      DFunLike.coe (F := C.X n →ₗ[R] M) c.val z.val := by
  dsimp only [evaluateLinearHomCocycle, AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass, LinearMap.comp_apply]
  simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rfl

/-- Canonical evaluation on homology, linear in the actual cocycle. -/
def linearHomCocycleEvaluation (C : ChainComplex (ModuleCat.{0} R) ℕ)
    (M : ModuleCat.{0} R) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (linearHomCochainComplex C M) n →ₗ[R] (C.homology n →ₗ[R] M) where
  toFun := evaluateLinearHomCocycle C M n
  map_add' c d := by
    ext h
    obtain ⟨z, rfl⟩ := AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_surjective C n h
    simp only [evaluateLinearHomCocycle_chainClass, LinearMap.add_apply, Submodule.coe_add]
    rfl
  map_smul' r c := by
    ext h
    obtain ⟨z, rfl⟩ := AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_surjective C n h
    simp only [evaluateLinearHomCocycle_chainClass, LinearMap.smul_apply,
      Submodule.coe_smul, RingHom.id_apply]
    rfl

/-- A Hom-complex boundary represents the zero functional on chain homology. -/
@[simp]
theorem linearHomCocycleEvaluation_boundary (C : ChainComplex (ModuleCat.{0} R) ℕ)
    (M : ModuleCat.{0} R) (n : ℕ)
    (c : ((linearHomCochainComplex C M).sc n).X₁) :
    linearHomCocycleEvaluation C M n
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainBoundaryMap (linearHomCochainComplex C M) n c) = 0 := by
  ext h
  obtain ⟨z, rfl⟩ := AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_surjective C n h
  change evaluateLinearHomCocycle C M n
    (AlgebraicTopology.Cohomology.Singular.Representatives.cochainBoundaryMap (linearHomCochainComplex C M) n c) (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass C n z) = 0
  rw [evaluateLinearHomCocycle_chainClass]
  exact linearHomCoboundary_cycle C M _ n c z

/-- Canonical evaluation from actual Hom-complex cohomology to linear maps on
actual categorical chain homology. -/
def linearHomHomologyEvaluation (C : ChainComplex (ModuleCat.{0} R) ℕ)
    (M : ModuleCat.{0} R) (n : ℕ) :
    (linearHomCochainComplex C M).homology n →ₗ[R] (C.homology n →ₗ[R] M) :=
  ((AlgebraicTopology.Cohomology.Singular.Representatives.cochainBoundaries (linearHomCochainComplex C M) n).liftQ
    (linearHomCocycleEvaluation C M n)
    (by
      intro c hc
      rcases hc with ⟨w, rfl⟩
      exact linearHomCocycleEvaluation_boundary C M n w)).comp
    (AlgebraicTopology.Cohomology.Singular.Representatives.cohomologyQuotientIso (linearHomCochainComplex C M) n).toLinearEquiv.toLinearMap

/-- The descended pairing is ordinary evaluation on any cycle and cocycle representatives. -/
@[simp]
theorem linearHomHomologyEvaluation_class_class (C : ChainComplex (ModuleCat.{0} R) ℕ)
    (M : ModuleCat.{0} R) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (linearHomCochainComplex C M) n) (z : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles C n) :
    linearHomHomologyEvaluation C M n
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (linearHomCochainComplex C M) n c) (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass C n z) =
        DFunLike.coe (F := C.X n →ₗ[R] M) c.val z.val := by
  dsimp only [linearHomHomologyEvaluation, AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass, LinearMap.comp_apply]
  simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  exact evaluateLinearHomCocycle_chainClass C M n c z

end Evaluation

variable {F : Type} [Field F]

/-- A dual-complex cocycle vanishing on cycles is an actual coboundary.
The extension of its factor through the differential follows from vector-space
duality and is not supplied as an assumption. -/
theorem dualCochainClass_eq_zero_of_vanishesOnCycles
    (C : ChainComplex (ModuleCat.{0} F) ℕ) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (dualCochainComplex C) n)
    (hc : ∀ z : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles C n, DFunLike.coe (F := C.X n →ₗ[F] F) c.val z.val = 0) :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (dualCochainComplex C) n c = 0 := by
  obtain ⟨ψ, hψ⟩ := AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.functionalFactors_of_vanishesOnKernel
    (C.sc n).g.hom (c.val : C.X n →ₗ[F] F) (fun z hz => hc ⟨z, hz⟩)
  let p : ((dualCochainComplex C).sc n).X₁ := ψ
  have hp : ((dualCochainComplex C).sc n).f p = c.val := by
    exact hψ
  apply (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_eq_zero_iff (dualCochainComplex C) n c).mpr
  exact ⟨p, Subtype.ext hp⟩

/-- Any linear functional on chain homology is evaluation by an actual dual-complex
cocycle, by extension from the cycle subspace. -/
theorem exists_dualCocycle_realizing_homologyFunctional
    (C : ChainComplex (ModuleCat.{0} F) ℕ) (n : ℕ) (L : C.homology n →ₗ[F] F) :
    ∃ c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (dualCochainComplex C) n,
      ∀ z : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles C n,
        DFunLike.coe (F := C.X n →ₗ[F] F) c.val z.val = L (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass C n z) := by
  obtain ⟨φ, hφ⟩ := (L.comp (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass C n)).exists_extend
  have hbound : φ.comp (C.sc n).f.hom = 0 := by
    ext z
    have hz := LinearMap.congr_fun hφ (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainBoundaryMap C n z)
    change φ ((C.sc n).f z) = L (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass C n (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainBoundaryMap C n z)) at hz
    rw [AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_boundary, map_zero] at hz
    exact hz
  have hc : φ ∈ AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (dualCochainComplex C) n := by
    exact hbound
  refine ⟨⟨φ, hc⟩, fun z => ?_⟩
  exact LinearMap.congr_fun hφ z

/-- Scalar Hom-complex cohomology is detected by its evaluations on chain homology. -/
theorem dualComplexHomologyEvaluation_injective
    (C : ChainComplex (ModuleCat.{0} F) ℕ) (n : ℕ) :
    Function.Injective (linearHomHomologyEvaluation C (ModuleCat.of F F) n) := by
  intro a b hab
  have hzero : linearHomHomologyEvaluation C (ModuleCat.of F F) n (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  obtain ⟨c, hc⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective (dualCochainComplex C) n (a - b)
  have hc0 : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (dualCochainComplex C) n c = 0 := by
    apply dualCochainClass_eq_zero_of_vanishesOnCycles C n c
    intro z
    have hz : linearHomHomologyEvaluation C (ModuleCat.of F F) n
        (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (dualCochainComplex C) n c) (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass C n z) = 0 := by
      rw [hc, hzero]
      rfl
    exact (linearHomHomologyEvaluation_class_class C (ModuleCat.of F F) n c z).symm.trans hz
  exact sub_eq_zero.mp (hc.symm.trans hc0)

/-- Every functional on homology arises from actual scalar Hom-complex cohomology. -/
theorem dualComplexHomologyEvaluation_surjective
    (C : ChainComplex (ModuleCat.{0} F) ℕ) (n : ℕ) :
    Function.Surjective (linearHomHomologyEvaluation C (ModuleCat.of F F) n) := by
  intro L
  obtain ⟨c, hc⟩ := exists_dualCocycle_realizing_homologyFunctional C n L
  refine ⟨AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (dualCochainComplex C) n c, ?_⟩
  ext h
  obtain ⟨z, rfl⟩ := AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_surjective C n h
  rw [linearHomHomologyEvaluation_class_class]
  exact hc z

/-- Universal-coefficient duality for any genuine chain complex of vector spaces,
in every nonnegative degree. Its forward map is canonical evaluation. -/
def dualComplexUniversalCoefficientEquiv
    (C : ChainComplex (ModuleCat.{0} F) ℕ) (n : ℕ) :
    (dualCochainComplex C).homology n ≃ₗ[F] Module.Dual F (C.homology n) :=
  LinearEquiv.ofBijective (linearHomHomologyEvaluation C (ModuleCat.of F F) n)
    ⟨dualComplexHomologyEvaluation_injective C n,
      dualComplexHomologyEvaluation_surjective C n⟩

@[simp]
theorem dualComplexUniversalCoefficientEquiv_apply
    (C : ChainComplex (ModuleCat.{0} F) ℕ) (n : ℕ)
    (c : (dualCochainComplex C).homology n) :
    dualComplexUniversalCoefficientEquiv C n c =
      linearHomHomologyEvaluation C (ModuleCat.of F F) n c := rfl

/-- On cycle and cocycle classes, the universal-coefficient equivalence is exactly
the original linear functional applied to the original vector. -/
@[simp]
theorem dualComplexUniversalCoefficientEquiv_class_class
    (C : ChainComplex (ModuleCat.{0} F) ℕ) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (dualCochainComplex C) n) (z : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles C n) :
    dualComplexUniversalCoefficientEquiv C n
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (dualCochainComplex C) n c) (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass C n z) =
        DFunLike.coe (F := C.X n →ₗ[F] F) c.val z.val :=
  linearHomHomologyEvaluation_class_class C (ModuleCat.of F F) n c z

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.DualComplexUniversalCoefficient.Cycles
