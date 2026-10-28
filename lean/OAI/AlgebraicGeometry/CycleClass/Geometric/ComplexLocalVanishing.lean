import OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexLocalTopHomology
import OAI.AlgebraicGeometry.CycleClass.Geometric.HomologyZeroNaturality

/-! # Complex Local Vanishing -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexLocalVanishing.Cycles

noncomputable section

/-!
# Concentration of complex normal local homology

The canonical zeroth-homology augmentations identify the inclusion map of a
path-connected subspace in a path-connected ambient space. The actual relative
long exact sequence then gives the low-degree vanishing needed for the pair
`(ℂ^p, ℂ^p \ {0})`. Together with the sphere calculation this proves that the
local integral singular homology is zero exactly outside degree `2p`.

The top group was already computed as `ℤ`. Neither this concentration result
nor that rank calculation asserts compatibility of generators with orientation
or chart changes.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false in
/-- The actual map induced on H0 by a subspace inclusion agrees with the
canonical augmentation identifications when both spaces are path connected. -/
theorem subspaceHomologyInclusion_zero_eq (X : TopCat.{0}) (A : Set X)
    [PathConnectedSpace X] [PathConnectedSpace A] :
    RelativeHomologyExact.Cycles.subspaceHomologyInclusion X A 0 =
      (ContractibleModel.Cycles.integralSingularH0Iso (TopCat.of A)).hom ≫ (ContractibleModel.Cycles.integralSingularH0Iso X).inv := by
  apply (cancel_mono (ContractibleModel.Cycles.integralSingularH0Iso X).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact HomologyZeroNaturality.Cycles.integralSingularH0_augmentation_naturality (LocalHomology.Cycles.subspaceInclusion X A)

/-- In particular this genuine H0 inclusion is an isomorphism. -/
instance subspaceHomologyInclusion_zero_isIso (X : TopCat.{0}) (A : Set X)
    [PathConnectedSpace X] [PathConnectedSpace A] :
    IsIso (RelativeHomologyExact.Cycles.subspaceHomologyInclusion X A 0) := by
  rw [subspaceHomologyInclusion_zero_eq]
  infer_instance

/-- The actual degree-zero relative group vanishes for a path-connected
subspace of a path-connected ambient space. -/
theorem relativeH0_isZero_of_pathConnected (X : TopCat.{0}) (A : Set X)
    [PathConnectedSpace X] [PathConnectedSpace A] :
    IsZero (LocalHomology.Cycles.relativeSingularHomology X A 0) := by
  apply IsZero.of_epi_eq_zero (RelativeHomologyExact.Cycles.relativeHomologyProjection X A 0)
  exact zero_of_epi_comp (RelativeHomologyExact.Cycles.subspaceHomologyInclusion X A 0)
    (RelativeHomologyExact.Cycles.subspaceHomologyInclusion_projection X A 0)

/-- If the ambient H1 vanishes as well, the actual relative H1 vanishes.
The connecting map is mono and its target's inclusion map is an isomorphism. -/
theorem relativeH1_isZero_of_pathConnected (X : TopCat.{0}) (A : Set X)
    [PathConnectedSpace X] [PathConnectedSpace A]
    (hambient : IsZero (RelativeHomologyExact.Cycles.integralSingularHomology X 1)) :
    IsZero (LocalHomology.Cycles.relativeSingularHomology X A 1) := by
  let : Mono (RelativeHomologyExact.Cycles.relativeHomologyBoundary X A 0) :=
    (LocalHomology.Cycles.relativeChainSequence_shortExact X A).mono_δ 1 0 rfl hambient
  apply IsZero.of_mono_eq_zero (RelativeHomologyExact.Cycles.relativeHomologyBoundary X A 0)
  exact zero_of_comp_mono (RelativeHomologyExact.Cycles.subspaceHomologyInclusion X A 0)
    (RelativeHomologyExact.Cycles.relativeHomologyBoundary_inclusion X A 0)

/-- Punctured positive-dimensional complex coordinate space is genuinely
path connected. The real coordinate model has dimension at least two. -/
instance positiveComplexPunctured_pathConnectedSpace (p : ℕ) :
    PathConnectedSpace (NormalSphere.Cycles.PuncturedNormal (Fin (p + 1) → ℂ)) := by
  have hdim : 1 < Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 * (p + 1)))) := by
    simp only [finrank_euclideanSpace_fin]
    omega
  let : PathConnectedSpace (NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin (2 * (p + 1))))) :=
    isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_compl_singleton_of_one_lt_rank
        (Module.one_lt_rank_of_one_lt_finrank hdim) 0)
  exact (RealComplexNormalModel.Cycles.complexRealPuncturedHomeomorph (p + 1)).symm.surjective.pathConnectedSpace
    (RealComplexNormalModel.Cycles.complexRealPuncturedHomeomorph (p + 1)).symm.continuous

/-- Local H0 vanishes in positive complex dimension. -/
theorem positiveComplexLocalH0_isZero (p : ℕ) :
    IsZero (LocalHomology.Cycles.localSingularHomology (TopCat.of (Fin (p + 1) → ℂ)) 0 0) :=
  relativeH0_isZero_of_pathConnected (TopCat.of (Fin (p + 1) → ℂ)) {0}ᶜ

/-- Local H1 vanishes in positive complex dimension. -/
theorem positiveComplexLocalH1_isZero (p : ℕ) :
    IsZero (LocalHomology.Cycles.localSingularHomology (TopCat.of (Fin (p + 1) → ℂ)) 0 1) :=
  relativeH1_isZero_of_pathConnected (TopCat.of (Fin (p + 1) → ℂ)) {0}ᶜ
    (ContractibleModel.Cycles.isZero_complexNormalModelHomology (p + 1) 1 (by decide))

/-- The zero-dimensional model has no local homology in positive degree.
Here the punctured subspace is empty, so the actual relative chain complex
is identified with the absolute one. -/
theorem complexZeroLocalHomology_isZero (n : ℕ) (hn : n ≠ 0) :
    IsZero (LocalHomology.Cycles.localSingularHomology (TopCat.of (Fin 0 → ℂ)) 0 n) := by
  have hempty : ({0}ᶜ : Set (Fin 0 → ℂ)) = ∅ := by
    ext x
    simp [Subsingleton.elim x 0]
  unfold LocalHomology.Cycles.localSingularHomology
  rw [hempty]
  exact (ContractibleModel.Cycles.isZero_complexNormalModelHomology 0 n hn).of_iso
    (Point.Cycles.relativeEmptyHomologyIso (TopCat.of (Fin 0 → ℂ)) n)

/-- Actual complex normal local homology vanishes outside the real dimension,
in every degree and including the zero-dimensional case. -/
theorem complexNormalLocalHomology_isZero (p n : ℕ) (hnotTop : n ≠ 2 * p) :
    IsZero (LocalHomology.Cycles.localSingularHomology (TopCat.of (Fin p → ℂ)) 0 n) := by
  cases p with
  | zero => exact complexZeroLocalHomology_isZero n (by simpa using hnotTop)
  | succ p =>
      cases n with
      | zero => exact positiveComplexLocalH0_isZero p
      | succ n =>
          cases n with
          | zero => exact positiveComplexLocalH1_isZero p
          | succ n =>
              exact ComplexLocalTopHomology.Cycles.positiveComplexNormalLocalHomology_isZero p (n + 1)
                (Nat.succ_ne_zero n) (by simpa only [Nat.mul_succ] using hnotTop)

/-- The top group is nonzero because its already-proved value is `ℤ`. -/
theorem complexNormalTopLocalHomology_not_isZero (p : ℕ) :
    ¬ IsZero (LocalHomology.Cycles.localSingularHomology (TopCat.of (Fin p → ℂ)) 0 (2 * p)) := by
  intro h
  have hZ := h.of_iso (ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso p).symm
  let : Subsingleton ℤ := ModuleCat.isZero_iff_subsingleton.mp hZ
  exact zero_ne_one (Subsingleton.elim (0 : ℤ) 1)

/-- The precise concentration statement: the genuine local group vanishes
if and only if its degree is different from `2p`. -/
theorem complexNormalLocalHomology_isZero_iff (p n : ℕ) :
    IsZero (LocalHomology.Cycles.localSingularHomology (TopCat.of (Fin p → ℂ)) 0 n) ↔ n ≠ 2 * p := by
  constructor
  · intro h hn
    subst n
    exact complexNormalTopLocalHomology_not_isZero p h
  · exact complexNormalLocalHomology_isZero p n

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexLocalVanishing.Cycles
