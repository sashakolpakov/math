import OAI.AlgebraicTopology.Cohomology.Singular.Augmentation
import OAI.AlgebraicTopology.Cohomology.Singular.StalkExactness
import OAI.AlgebraicTopology.Cohomology.Singular.SheafQuasiIso
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Topology.Sheaves.Sheafify
import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Algebra.Homology.QuasiIso

/-! # Sheaf Resolution -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.SheafResolution

noncomputable section

/-!
# The sheafified singular cochain resolution

The complex in this file is the degreewise sheafification of the genuine
singular cochain presheaf. The independently defined sheaf of locally constant
complex functions maps to its degree zero. Its kernel property and the local
singular primitive theorem give the resolution property.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.AlgebraicTopology.Cohomology.Singular.Augmentation.Comparison

/-- The actual singular cochain presheaf, sheafified in each degree. -/
def singularSheafComplex (X : TopCat.{0}) :
    CochainComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X)
      (ModuleCat.{0} ℂ)) ℕ :=
  ((presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℂ ℂ) X)

/-- The degree objects are sheafifications of genuine singular cochain presheaves. -/
@[simp]
theorem singularSheafComplex_X (X : TopCat.{0}) (n : ℕ) :
    (singularSheafComplex X).X n =
      (presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)).obj
        (DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf (ModuleCat.of ℂ ℂ) X n) := rfl

/-- The differential is the sheafification of the ordinary singular coboundary. -/
@[simp]
theorem singularSheafComplex_d (X : TopCat.{0}) (i j : ℕ) :
    (singularSheafComplex X).d i j =
      (presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)).map
        ((DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℂ ℂ) X).d i j) := rfl

/-- Sheafification of the literal point-evaluation augmentation, using the
canonical isomorphism from the existing locally constant sheaf to its sheafification. -/
def locallyConstantSingularSheafAugmentation (X : TopCat.{0}) :
    (DeRham.Comparison.LocallyConstantSheaf.locallyConstantSheaf X : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
      (ModuleCat.{0} ℂ)) ⟶ (singularSheafComplex X).X 0 :=
  (sheafificationIso (DeRham.Comparison.LocallyConstantSheaf.locallyConstantSheaf X :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ))).hom ≫
    (presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)).map
      (Augmentation.Comparison.locallyConstantSingularAugmentation X)

/-- On underlying presheaves, the sheaf augmentation is literal point evaluation
followed by the actual sheafification unit. -/
theorem locallyConstantSingularSheafAugmentation_hom (X : TopCat.{0}) :
    (locallyConstantSingularSheafAugmentation X).hom =
      Augmentation.Comparison.locallyConstantSingularAugmentation X ≫
        CategoryTheory.toSheafify (Opens.grothendieckTopology X)
          (DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf (ModuleCat.of ℂ ℂ) X 0) :=
  (CategoryTheory.toSheafify_naturality (Opens.grothendieckTopology X)
    (Augmentation.Comparison.locallyConstantSingularAugmentation X)).symm

/-- The sheaf augmentation is annihilated by the first differential. -/
theorem locallyConstantSingularSheafAugmentation_d (X : TopCat.{0}) :
    locallyConstantSingularSheafAugmentation X ≫ (singularSheafComplex X).d 0 1 = 0 := by
  let S := (show ShortComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{0} ℂ) from
    Augmentation.Comparison.singularAugmentationShortComplex X).map
      (presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ))
  change ((sheafificationIso (DeRham.Comparison.LocallyConstantSheaf.locallyConstantSheaf X :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ))).hom ≫
    S.f) ≫ S.g = 0
  rw [Category.assoc, S.zero, comp_zero]

/-- The augmentation remains injective in the category of actual sheaves. -/
instance locallyConstantSingularSheafAugmentation_mono (X : TopCat.{0}) :
    Mono (locallyConstantSingularSheafAugmentation X) := by
  let ε : (DeRham.Comparison.LocallyConstantSheaf.locallyConstantPresheaf X : (Opens X)ᵒᵖ ⥤ ModuleCat.{0} ℂ) ⟶
      DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf (ModuleCat.of ℂ ℂ) X 0 :=
    Augmentation.Comparison.locallyConstantSingularAugmentation X
  have : Mono ε := Augmentation.Comparison.locallyConstantSingularAugmentation_mono X
  let F := presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)
  let e : (DeRham.Comparison.LocallyConstantSheaf.locallyConstantSheaf X :
      CategoryTheory.Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)) ≅
      F.obj (DeRham.Comparison.LocallyConstantSheaf.locallyConstantPresheaf X) := sheafificationIso (DeRham.Comparison.LocallyConstantSheaf.locallyConstantSheaf X)
  have : Mono (F.map ε) := Functor.map_mono F ε
  have : Mono e.hom := by infer_instance
  change Mono (e.hom ≫ F.map ε)
  infer_instance

/-- The degree-zero augmented sequence of actual singular cochain sheaves. -/
def singularSheafAugmentationShortComplex (X : TopCat.{0}) :
    ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X)
      (ModuleCat.{0} ℂ)) :=
  ShortComplex.mk (locallyConstantSingularSheafAugmentation X)
    ((singularSheafComplex X).d 0 1) (locallyConstantSingularSheafAugmentation_d X)

/-- The augmented sheaf sequence is canonically the sheafification of the
already verified augmented presheaf sequence. -/
def singularSheafAugmentationShortComplexIso (X : TopCat.{0}) :
    singularSheafAugmentationShortComplex X ≅
      (show ShortComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{0} ℂ) from
        Augmentation.Comparison.singularAugmentationShortComplex X).map
        (presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)) :=
  ShortComplex.isoMk (sheafificationIso (DeRham.Comparison.LocallyConstantSheaf.locallyConstantSheaf X :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)))
    (Iso.refl _) (Iso.refl _)
    (by simp [singularSheafAugmentationShortComplex,
      locallyConstantSingularSheafAugmentation, Augmentation.Comparison.singularAugmentationShortComplex])
    (by simp [singularSheafAugmentationShortComplex, Augmentation.Comparison.singularAugmentationShortComplex])

/-- Sheafification preserves the proved degree-zero exactness. -/
theorem singularSheafAugmentationShortComplex_exact (X : TopCat.{0})
    [LocallyPathConnectedSpace X] : (singularSheafAugmentationShortComplex X).Exact := by
  apply (ShortComplex.exact_iff_of_iso (singularSheafAugmentationShortComplexIso X)).2
  have h : (show ShortComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{0} ℂ) from
      Augmentation.Comparison.singularAugmentationShortComplex X).Exact := Augmentation.Comparison.singularAugmentationShortComplex_exact X
  exact h.map
    (presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ))

/-- The locally constant augmentation is the categorical kernel of the
degree-zero differential in the sheafified singular complex. -/
def locallyConstantSingularSheafAugmentation_isKernel (X : TopCat.{0})
    [LocallyPathConnectedSpace X] :
    IsLimit (KernelFork.ofι (locallyConstantSingularSheafAugmentation X)
      (locallyConstantSingularSheafAugmentation_d X)) := by
  haveI : Mono (singularSheafAugmentationShortComplex X).f :=
    locallyConstantSingularSheafAugmentation_mono X
  exact (singularSheafAugmentationShortComplex_exact X).fIsKernel

/-- The locally constant sheaf, concentrated in degree zero, maps to the
actual sheafified singular cochain complex by point evaluation. -/
def singularSheafResolutionMap (X : TopCat.{0}) :
    (CochainComplex.single₀ (CategoryTheory.Sheaf (Opens.grothendieckTopology X)
      (ModuleCat.{0} ℂ))).obj (DeRham.Comparison.LocallyConstantSheaf.locallyConstantSheaf X) ⟶ singularSheafComplex X :=
  (CochainComplex.fromSingle₀Equiv (singularSheafComplex X) (DeRham.Comparison.LocallyConstantSheaf.locallyConstantSheaf X)).symm
    ⟨locallyConstantSingularSheafAugmentation X, locallyConstantSingularSheafAugmentation_d X⟩

/-- The chain map uses precisely the verified degree-zero augmentation. -/
@[simp]
theorem singularSheafResolutionMap_f_zero (X : TopCat.{0}) :
    (singularSheafResolutionMap X).f 0 = locallyConstantSingularSheafAugmentation X :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

/-- The augmentation induces an isomorphism in degree-zero cohomology on
locally path-connected spaces. -/
theorem singularSheafResolutionMap_quasiIsoAt_zero (X : TopCat.{0})
    [LocallyPathConnectedSpace X] : QuasiIsoAt (singularSheafResolutionMap X) 0 := by
  rw [CochainComplex.quasiIsoAt₀_iff]
  apply (ShortComplex.quasiIso_iff_of_zeros _ (by rfl) (by rfl)
    (by
      change (singularSheafComplex X).d 0 0 = 0
      exact (singularSheafComplex X).shape 0 0 (by simp))).2
  change (ShortComplex.mk ((singularSheafResolutionMap X).f 0)
    ((singularSheafComplex X).d 0 1) _).Exact ∧
    Mono ((singularSheafResolutionMap X).f 0)
  simpa only [singularSheafResolutionMap_f_zero, singularSheafAugmentationShortComplex] using
    (And.intro (singularSheafAugmentationShortComplex_exact X)
      (locallyConstantSingularSheafAugmentation_mono X))

/-- Positive-degree exactness passes from the proved singular stalk complex
to the sheafified complex through the actual sheafification stalk isomorphism. -/
theorem singularSheafComplex_exactAt_succ (X : TopCat.{0})
    [StronglyLocallyContractibleSpace X] (n : ℕ) :
    (singularSheafComplex X).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff]
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact
    (show ShortComplex (TopCat.Sheaf (ModuleCat.{0} ℂ) X) from
      (singularSheafComplex X).sc (n + 1))).2
  intro x
  change (SheafQuasiIso.sheafStalkCochainComplex (singularSheafComplex X) x).ExactAt (n + 1)
  exact (StalkExactness.singularStalkComplex_exactAt_succ (ModuleCat.of ℂ ℂ) X x n).of_iso
    (SheafQuasiIso.sheafificationStalkComplexIso (DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℂ ℂ) X) x)

/-- All positive cohomology sheaves of this actual complex vanish on a strongly
locally contractible space. -/
theorem isZero_singularSheafCohomology_succ (X : TopCat.{0})
    [StronglyLocallyContractibleSpace X] (n : ℕ) :
    IsZero ((singularSheafComplex X).homology (n + 1)) :=
  (singularSheafComplex_exactAt_succ X n).isZero_homology

/-- The genuine locally constant sheaf is resolved by the sheafified singular
cochain complex on a strongly locally contractible space. -/
theorem quasiIso_singularSheafResolutionMap (X : TopCat.{0})
    [StronglyLocallyContractibleSpace X] : QuasiIso (singularSheafResolutionMap X) := by
  apply (quasiIso_iff _).2
  intro n
  cases n with
  | zero => exact singularSheafResolutionMap_quasiIsoAt_zero X
  | succ n =>
    apply (quasiIsoAt_iff_exactAt _ _
      (HomologicalComplex.exactAt_single_obj (ComplexShape.up ℕ) 0
        (DeRham.Comparison.LocallyConstantSheaf.locallyConstantSheaf X : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
          (ModuleCat.{0} ℂ)) (n + 1) (Nat.succ_ne_zero n))).2
    exact singularSheafComplex_exactAt_succ X n

/-- Real normed manifold charts supply the local topology needed for the
resolution, with no independent local contractibility assumption. -/
theorem quasiIso_singularSheafResolutionMap_of_chartedSpace
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : TopCat.{0}) [ChartedSpace E X] : QuasiIso (singularSheafResolutionMap X) := by
  let := ChartLocalContractible.stronglyLocallyContractibleSpace_of_chartedSpace E X
  exact quasiIso_singularSheafResolutionMap X

end

end OAI.AlgebraicTopology.Cohomology.Singular.SheafResolution
