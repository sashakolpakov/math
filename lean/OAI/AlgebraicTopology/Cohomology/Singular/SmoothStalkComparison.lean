import OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothPresheaf
import OAI.AlgebraicTopology.Cohomology.Singular.ChartSmoothComparison
import OAI.AlgebraicTopology.DeRham.Comparison.SingularPresheaf
import OAI.AlgebraicTopology.Cohomology.Singular.Stalk
import OAI.AlgebraicTopology.Cohomology.Singular.StalkLocalIso

/-! # Smooth Stalk Comparison -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.SmoothStalkComparison

noncomputable section

/-!
# The actual continuous-to-smooth comparison on stalk complexes

The cochain map is formed from restriction of ordinary singular cochains to
the genuine manifold-smooth singular simplices on every open set. Its map on
stalks is the degreewise map of the actual filtered-colimit stalk functor.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace
open _root_.TopCat.Presheaf
open scoped _root_.Manifold ContDiff _root_.Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (M : Type) [TopologicalSpace M] [ChartedSpace E M]
variable {R : Type} [Ring R]

/-- The actual restriction to smooth simplices as a map of complexes of
module-valued presheaves. -/
def manifoldSmoothPresheafRestriction (A : ModuleCat.{0} R) :
    DeRham.Comparison.SingularPresheaf.singularPresheafComplex A (TopCat.of M) ⟶
      ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E M A where
  f n :=
    { app := fun U => (ManifoldSmooth.manifoldSmoothCochainRestriction E A U.unop).f n
      naturality := fun U V i => congrArg (fun f => f.f n)
        ((ManifoldSmoothPresheaf.manifoldSmoothRestrictionNatTrans E M A).naturality i) }
  comm' i j _ := by
    apply NatTrans.ext
    funext U
    exact (ManifoldSmooth.manifoldSmoothCochainRestriction E A U.unop).comm i j

@[simp]
theorem manifoldSmoothPresheafRestriction_f_app (A : ModuleCat.{0} R)
    (U : Opens M) (n : ℕ) :
    ((manifoldSmoothPresheafRestriction E M A).f n).app (op U) =
      (ManifoldSmooth.manifoldSmoothCochainRestriction E A U).f n := rfl

/-- The induced comparison between the ordinary and smooth singular stalk
complexes, obtained by applying the actual stalk functor in every degree. -/
def manifoldSmoothStalkRestriction (A : ModuleCat.{0} R) (x : M) :
    (((stalkFunctor (X := TopCat.of M) (ModuleCat.{0} R) x).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (DeRham.Comparison.SingularPresheaf.singularPresheafComplex A (TopCat.of M))) ⟶
    (((stalkFunctor (X := TopCat.of M) (ModuleCat.{0} R) x).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E M A)) :=
  ((stalkFunctor (X := TopCat.of M) (ModuleCat.{0} R) x).mapHomologicalComplex
    (ComplexShape.up ℕ)).map (manifoldSmoothPresheafRestriction E M A)

/-- If ordinary-to-smooth restriction is a quasi-isomorphism on an open set,
the corresponding component of the cohomology presheaf map is an isomorphism.
This uses the canonical evaluation--cohomology comparison. -/
theorem isIso_manifoldSmoothPresheafRestriction_homology_app
    (A : ModuleCat.{0} R) (U : Opens M)
    [QuasiIso (ManifoldSmooth.manifoldSmoothCochainRestriction E A U)] (n : ℕ) :
    IsIso ((HomologicalComplex.homologyMap
      (manifoldSmoothPresheafRestriction E M A) n).app (op U)) := by
  let f := manifoldSmoothPresheafRestriction E M A
  have : IsIso (HomologicalComplex.homologyMap
      (((Stalk.presheafSectionFunctor (X := TopCat.of M) U).mapHomologicalComplex
        (ComplexShape.up ℕ)).map f) n) := by
    change IsIso (HomologicalComplex.homologyMap
      (ManifoldSmooth.manifoldSmoothCochainRestriction E A U) n)
    infer_instance
  have : IsIso ((Stalk.openCohomologyIso
      (DeRham.Comparison.SingularPresheaf.singularPresheafComplex A (TopCat.of M)) U n).hom ≫
      (HomologicalComplex.homologyMap f n).app (op U)) := by
    rw [← Stalk.openCohomologyIso_naturality f U n]
    infer_instance
  exact IsIso.of_isIso_comp_left
    (Stalk.openCohomologyIso (DeRham.Comparison.SingularPresheaf.singularPresheafComplex A (TopCat.of M)) U n).hom
    ((HomologicalComplex.homologyMap f n).app (op U))

variable [IsManifold 𝓘(ℝ, E) ∞ M]

/-- On a smooth manifold, restriction to genuine smooth singular simplices
induces an isomorphism on the stalk of every cohomology presheaf. -/
theorem isIso_manifoldSmoothPresheafRestriction_homology_stalk
    (A : ModuleCat.{0} R) (x : M) (n : ℕ) :
    IsIso ((stalkFunctor (X := TopCat.of M) (ModuleCat.{0} R) x).map
      (HomologicalComplex.homologyMap (manifoldSmoothPresheafRestriction E M A) n)) := by
  apply StalkLocalIso.stalkMap_isIso_of_locally_isIso
  intro U hxU
  obtain ⟨V, hxV, hVU, hV⟩ :=
    ChartSmoothComparison.exists_open_smoothComparison_subset E A x (U.isOpen.mem_nhds hxU)
  let := hV
  exact ⟨V, hxV, homOfLE hVU,
    isIso_manifoldSmoothPresheafRestriction_homology_app E M A V n⟩

/-- The actual map between stalk complexes is a quasi-isomorphism. Its proof
uses genuine chart-ball comparison and exactness of filtered colimits. -/
theorem quasiIso_manifoldSmoothStalkRestriction
    (A : ModuleCat.{0} R) (x : M) :
    QuasiIso (manifoldSmoothStalkRestriction E M A x) := by
  constructor
  intro n
  apply (quasiIsoAt_iff_isIso_homologyMap _ n).2
  have := isIso_manifoldSmoothPresheafRestriction_homology_stalk E M A x n
  have : IsIso (HomologicalComplex.homologyMap
      (manifoldSmoothStalkRestriction E M A x) n ≫
      (Stalk.stalkCohomologyIso (X := TopCat.of M)
        (ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E M A) x n).hom) := by
    change IsIso (HomologicalComplex.homologyMap
      (((stalkFunctor (X := TopCat.of M) (ModuleCat.{0} R) x).mapHomologicalComplex
        (ComplexShape.up ℕ)).map (manifoldSmoothPresheafRestriction E M A)) n ≫ _)
    rw [Stalk.stalkCohomologyIso_naturality]
    infer_instance
  exact IsIso.of_isIso_comp_right
    (HomologicalComplex.homologyMap (manifoldSmoothStalkRestriction E M A x) n)
    (Stalk.stalkCohomologyIso (X := TopCat.of M)
      (ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E M A) x n).hom

/-- The canonical cohomology comparison between the ordinary and smooth
singular stalk complexes. -/
def manifoldSmoothStalkCohomologyIso (A : ModuleCat.{0} R) (x : M) (n : ℕ) :
    (Stalk.stalkCochainComplex (DeRham.Comparison.SingularPresheaf.singularPresheafComplex A (TopCat.of M)) x).homology n ≅
      (Stalk.stalkCochainComplex (X := TopCat.of M)
        (ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E M A) x).homology n := by
  letI := quasiIso_manifoldSmoothStalkRestriction E M A x
  exact isoOfQuasiIsoAt (manifoldSmoothStalkRestriction E M A x) n

@[simp]
theorem manifoldSmoothStalkCohomologyIso_hom (A : ModuleCat.{0} R) (x : M) (n : ℕ) :
    (manifoldSmoothStalkCohomologyIso E M A x n).hom =
      HomologicalComplex.homologyMap (manifoldSmoothStalkRestriction E M A x) n := rfl

end

end OAI.AlgebraicTopology.Cohomology.Singular.SmoothStalkComparison
