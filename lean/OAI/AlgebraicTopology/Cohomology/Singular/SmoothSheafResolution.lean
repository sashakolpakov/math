import OAI.AlgebraicTopology.Cohomology.Singular.SmoothStalkComparison
import OAI.AlgebraicTopology.Cohomology.Singular.SheafResolution

/-! # Smooth Sheaf Resolution -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution

noncomputable section

/-!
# The genuine smooth singular sheaf resolution

Sheafification of restriction from ordinary singular cochains to actual smooth
singular cochains is a quasi-isomorphism. The literal point-evaluation
augmentation of the locally constant sheaf therefore gives a resolution by
the sheafified smooth singular complex. Every comparison here is induced by
the actual restriction map and the actual sheafification unit.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff Simplicial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (M : Type) [TopologicalSpace M] [ChartedSpace E M]
variable {R : Type} [Ring R]

/-- The degreewise sheafification of the actual smooth singular presheaf complex. -/
def manifoldSmoothSheafComplex (A : ModuleCat.{0} R) :
    CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) (TopCat.of M)) ℕ :=
  SheafQuasiIso.sheafifiedCochainComplex (X := TopCat.of M) (ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E M A)

/-- The comparison is the sheafification of restriction to smooth simplices. -/
def manifoldSmoothSheafRestriction (A : ModuleCat.{0} R) :
    SheafQuasiIso.sheafifiedCochainComplex (DeRham.Comparison.SingularPresheaf.singularPresheafComplex A (TopCat.of M)) ⟶
      manifoldSmoothSheafComplex E M A :=
  ((presheafToSheaf (Opens.grothendieckTopology (TopCat.of M))
    (ModuleCat.{0} R)).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (SmoothStalkComparison.manifoldSmoothPresheafRestriction E M A)

@[simp]
theorem manifoldSmoothSheafRestriction_f_hom (A : ModuleCat.{0} R) (n : ℕ) :
    ((manifoldSmoothSheafRestriction E M A).f n).hom =
      CategoryTheory.sheafifyMap (Opens.grothendieckTopology (TopCat.of M))
        ((SmoothStalkComparison.manifoldSmoothPresheafRestriction E M A).f n) := rfl

/-- The comparison commutes with the genuine sheafification units in every degree. -/
theorem manifoldSmoothSheafRestriction_unit (A : ModuleCat.{0} R) (n : ℕ) :
    CategoryTheory.toSheafify (Opens.grothendieckTopology (TopCat.of M))
        ((DeRham.Comparison.SingularPresheaf.singularPresheafComplex A (TopCat.of M)).X n) ≫
        ((manifoldSmoothSheafRestriction E M A).f n).hom =
      (SmoothStalkComparison.manifoldSmoothPresheafRestriction E M A).f n ≫
        CategoryTheory.toSheafify (Opens.grothendieckTopology (TopCat.of M))
          ((ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E M A).X n) :=
  (CategoryTheory.toSheafify_naturality _ _).symm

/-- The proved comparison on every genuine stalk gives the sheaf quasi-isomorphism. -/
theorem quasiIso_manifoldSmoothSheafRestriction [IsManifold 𝓘(ℝ, E) ∞ M]
    (A : ModuleCat.{0} R) : QuasiIso (manifoldSmoothSheafRestriction E M A) := by
  apply (SheafQuasiIso.sheafified_quasiIso_iff_stalk (SmoothStalkComparison.manifoldSmoothPresheafRestriction E M A)).2
  intro x
  exact SmoothStalkComparison.quasiIso_manifoldSmoothStalkRestriction E M A x

/-- The induced isomorphism of cohomology sheaves for actual smooth restriction. -/
def manifoldSmoothSheafCohomologyIso [IsManifold 𝓘(ℝ, E) ∞ M]
    (A : ModuleCat.{0} R) (n : ℕ) :
    (SheafQuasiIso.sheafifiedCochainComplex (DeRham.Comparison.SingularPresheaf.singularPresheafComplex A (TopCat.of M))).homology n ≅
      (manifoldSmoothSheafComplex E M A).homology n := by
  letI := quasiIso_manifoldSmoothSheafRestriction E M A
  exact isoOfQuasiIsoAt (manifoldSmoothSheafRestriction E M A) n

@[simp]
theorem manifoldSmoothSheafCohomologyIso_hom [IsManifold 𝓘(ℝ, E) ∞ M]
    (A : ModuleCat.{0} R) (n : ℕ) :
    (manifoldSmoothSheafCohomologyIso E M A n).hom =
      HomologicalComplex.homologyMap (manifoldSmoothSheafRestriction E M A) n := rfl

/-- Locally constant complex functions give literal point-evaluation smooth zero-cochains. -/
def locallyConstantManifoldSmoothAugmentation :
    DeRham.Comparison.LocallyConstantSheaf.locallyConstantPresheaf (TopCat.of M) ⟶
      (ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E M (ModuleCat.of ℂ ℂ)).X 0 :=
  Augmentation.Comparison.locallyConstantSingularAugmentation (TopCat.of M) ≫
    (SmoothStalkComparison.manifoldSmoothPresheafRestriction E M (ModuleCat.of ℂ ℂ)).f 0

/-- On every actual smooth zero-simplex, the augmentation evaluates the
locally constant function at the point represented by that simplex. -/
@[simp]
theorem locallyConstantManifoldSmoothAugmentation_apply (U : Opens M)
    (f : LocallyConstant U ℂ)
    (s : (ManifoldSmooth.manifoldSmoothSingularSubcomplex E U).toSSet _⦋0⦌) :
    (Coefficients.degreewiseFunctionIso (ManifoldSmooth.manifoldSmoothSingularSubcomplex E U).toSSet
      (ModuleCat.of ℂ ℂ) 0).hom
        ((locallyConstantManifoldSmoothAugmentation E M).app (op U) f) s =
      f (TopCat.toSSetObj₀Equiv ((ManifoldSmooth.manifoldSmoothInclusion E U).app _ s)) := by
  change (Coefficients.degreewiseFunctionIso (ManifoldSmooth.manifoldSmoothSingularSubcomplex E U).toSSet
      (ModuleCat.of ℂ ℂ) 0).hom
        ((Singular.Functor.simplicialPullback (ModuleCat.of ℂ ℂ) (ManifoldSmooth.manifoldSmoothInclusion E U)).f 0
          ((Augmentation.Comparison.locallyConstantSingularAugmentation (TopCat.of M)).app (op U) f)) s = _
  rw [Formulas.degreewiseFunctionIso_pullback, ← Augmentation.singularZeroCochainPointIso_apply_simplex]
  exact Augmentation.Comparison.locallyConstantSingularAugmentation_apply (TopCat.of M) U f _

/-- The smooth point-evaluation augmentation has zero coboundary. -/
theorem locallyConstantManifoldSmoothAugmentation_d :
    locallyConstantManifoldSmoothAugmentation E M ≫
      (ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E M (ModuleCat.of ℂ ℂ)).d 0 1 = 0 := by
  rw [locallyConstantManifoldSmoothAugmentation, Category.assoc,
    (SmoothStalkComparison.manifoldSmoothPresheafRestriction E M (ModuleCat.of ℂ ℂ)).comm,
    ← Category.assoc, Augmentation.Comparison.locallyConstantSingularAugmentation_d, zero_comp]

/-- Sheafification of the literal smooth point-evaluation augmentation. -/
def locallyConstantManifoldSmoothSheafAugmentation :
    DeRham.Comparison.LocallyConstantSheaf.locallyConstantSheaf (TopCat.of M) ⟶
      (manifoldSmoothSheafComplex E M (ModuleCat.of ℂ ℂ)).X 0 :=
  (sheafificationIso (DeRham.Comparison.LocallyConstantSheaf.locallyConstantSheaf (TopCat.of M) :
    TopCat.Sheaf (ModuleCat.{0} ℂ) (TopCat.of M))).hom ≫
    (presheafToSheaf (Opens.grothendieckTopology (TopCat.of M)) (ModuleCat.{0} ℂ)).map
      (locallyConstantManifoldSmoothAugmentation E M)

/-- The actual sheaf augmentation is the literal presheaf augmentation followed
by the actual sheafification unit. -/
theorem locallyConstantManifoldSmoothSheafAugmentation_hom :
    (locallyConstantManifoldSmoothSheafAugmentation E M).hom =
      locallyConstantManifoldSmoothAugmentation E M ≫
        CategoryTheory.toSheafify (Opens.grothendieckTopology (TopCat.of M))
          ((ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E M (ModuleCat.of ℂ ℂ)).X 0) :=
  (CategoryTheory.toSheafify_naturality _ _).symm

/-- The sheaf augmentation is compatible with the verified ordinary singular
augmentation under the actual ordinary-to-smooth comparison. -/
theorem locallyConstantManifoldSmoothSheafAugmentation_eq_singular_comp :
    locallyConstantManifoldSmoothSheafAugmentation E M =
      SheafResolution.locallyConstantSingularSheafAugmentation (TopCat.of M) ≫
        (manifoldSmoothSheafRestriction E M (ModuleCat.of ℂ ℂ)).f 0 := by
  simp only [locallyConstantManifoldSmoothSheafAugmentation,
    locallyConstantManifoldSmoothAugmentation, Functor.map_comp,
    SheafResolution.locallyConstantSingularSheafAugmentation, Category.assoc]
  rfl

/-- The actual augmentation chain map to the sheafified smooth singular complex. -/
def manifoldSmoothSheafResolutionMap :
    (CochainComplex.single₀ (TopCat.Sheaf (ModuleCat.{0} ℂ) (TopCat.of M))).obj
      (DeRham.Comparison.LocallyConstantSheaf.locallyConstantSheaf (TopCat.of M)) ⟶
        manifoldSmoothSheafComplex E M (ModuleCat.of ℂ ℂ) :=
  SheafResolution.singularSheafResolutionMap (TopCat.of M) ≫
    manifoldSmoothSheafRestriction E M (ModuleCat.of ℂ ℂ)

/-- The resolution uses precisely the independently stated smooth augmentation. -/
@[simp]
theorem manifoldSmoothSheafResolutionMap_f_zero :
    (manifoldSmoothSheafResolutionMap E M).f 0 =
      locallyConstantManifoldSmoothSheafAugmentation E M := by
  rw [locallyConstantManifoldSmoothSheafAugmentation_eq_singular_comp]
  simp only [manifoldSmoothSheafResolutionMap, HomologicalComplex.comp_f,
    SheafResolution.singularSheafResolutionMap_f_zero]

/-- The locally constant sheaf is resolved by the genuine sheafified smooth
singular cochains on every smooth manifold modeled on a real normed space. -/
theorem quasiIso_manifoldSmoothSheafResolutionMap [IsManifold 𝓘(ℝ, E) ∞ M] :
    QuasiIso (manifoldSmoothSheafResolutionMap E M) := by
  have := SheafResolution.quasiIso_singularSheafResolutionMap_of_chartedSpace E (TopCat.of M)
  have := quasiIso_manifoldSmoothSheafRestriction E M (ModuleCat.of ℂ ℂ)
  exact quasiIso_comp _ _

end

end OAI.AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution
