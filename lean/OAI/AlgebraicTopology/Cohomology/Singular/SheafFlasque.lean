import OAI.AlgebraicTopology.Cohomology.Singular.CochainFlasque
import OAI.AlgebraicTopology.Cohomology.Singular.OpenSheafComparison
import OAI.AlgebraicTopology.Cohomology.Singular.SheafResolution
import OAI.AlgebraicTopology.Cohomology.Singular.OpenParacompact

/-! # Sheaf Flasque -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.SheafFlasque

noncomputable section

/-!
# Flasqueness of genuine sheafified singular cochains

The actual sheafification unit is surjective on every open section under
the stated paracompactness and Hausdorff hypotheses. The actual singular
cochain restrictions are surjective by extension by zero. Naturality then
proves mathlib's flasqueness property for the sheafified complex in every
degree. Metrizable spaces, and hence the stated finite-dimensional
manifolds, satisfy the open-subspace hypotheses.
-/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped _root_.Manifold

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type} [Ring R]

/-- Restriction of actual sheafified singular cochains is degreewise
surjective as soon as the smaller open subspace is paracompact Hausdorff. -/
theorem singularSheafSectionsRestriction_f_surjective_of_paracompact
    (A : ModuleCat.{0} R) (X : TopCat.{0}) {U V : Opens X} (i : U ⟶ V)
    [ParacompactSpace U] [T2Space U] (n : ℕ) :
    Function.Surjective ((OpenSheafComparison.singularSheafSectionsRestriction A X i).f n) := by
  intro s
  obtain ⟨a, ha⟩ := OpenSheafComparison.singularCochain_sheafification_open_surjective_of_paracompact A X U n s
  obtain ⟨b, hb⟩ := CochainFlasque.singularCochainDegreePresheaf_map_surjective A X n i a
  let η := CategoryTheory.toSheafify (Opens.grothendieckTopology X)
    (DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf A X n)
  refine ⟨η.app (op V) b, ?_⟩
  have h := ConcreteCategory.congr_hom (η.naturality i.op) b
  change η.app (op U) ((DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf A X n).map i.op b) =
    (OpenSheafComparison.singularSheafSectionsRestriction A X i).f n (η.app (op V) b) at h
  rw [hb] at h
  exact h.symm.trans ha

/-- The genuine restriction of sheafified section complexes is an
epimorphism under the same hypothesis on the smaller open set. -/
theorem singularSheafSectionsRestriction_epi_of_paracompact
    (A : ModuleCat.{0} R) (X : TopCat.{0}) {U V : Opens X} (i : U ⟶ V)
    [ParacompactSpace U] [T2Space U] :
    Epi (OpenSheafComparison.singularSheafSectionsRestriction A X i) :=
  HomologicalComplex.epi_of_epi_f _ (fun n => (ModuleCat.epi_iff_surjective _).mpr
    (singularSheafSectionsRestriction_f_surjective_of_paracompact A X i n))

/-- The genuine degreewise sheafification of singular cochains is flasque
when all open subspaces are paracompact and the ambient space is Hausdorff. -/
theorem sheafifiedSingularCochains_isFlasque_of_open_paracompact
    (A : ModuleCat.{0} R) (X : TopCat.{0}) [T2Space X]
    (hpara : ∀ U : Opens X, ParacompactSpace U) (n : ℕ) :
    TopCat.Sheaf.IsFlasque
      ((SheafQuasiIso.sheafifiedCochainComplex (DeRham.Comparison.SingularPresheaf.singularPresheafComplex A X)).X n) := by
  have := CochainFlasque.singularCochainDegreePresheaf_isFlasque A X n
  apply CochainFlasque.presheaf_isFlasque_of_pointwise_epi
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
      (DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf A X n))
  intro U
  have := hpara U.unop
  exact (ModuleCat.epi_iff_surjective _).mpr
    (OpenSheafComparison.singularCochain_sheafification_open_surjective_of_paracompact A X U.unop n)

/-- Every actual restriction of sections of a sheafified singular cochain
degree is surjective under the explicit open-subspace hypotheses. -/
theorem sheafifiedSingularCochains_restriction_surjective_of_open_paracompact
    (A : ModuleCat.{0} R) (X : TopCat.{0}) [T2Space X]
    (hpara : ∀ U : Opens X, ParacompactSpace U) (n : ℕ)
    {U V : Opens X} (i : U ⟶ V) :
    Function.Surjective
      (((SheafQuasiIso.sheafifiedCochainComplex (DeRham.Comparison.SingularPresheaf.singularPresheafComplex A X)).X n).obj.map i.op) := by
  have := sheafifiedSingularCochains_isFlasque_of_open_paracompact A X hpara n
  exact (ModuleCat.epi_iff_surjective _).mp inferInstance

/-- The same result for the already installed complex singular sheaf
resolution, with its exact existing degree objects. -/
theorem singularSheafComplex_X_isFlasque_of_open_paracompact
    (X : TopCat.{0}) [T2Space X]
    (hpara : ∀ U : Opens X, ParacompactSpace U) (n : ℕ) :
    TopCat.Sheaf.IsFlasque ((SheafResolution.singularSheafComplex X).X n) :=
  sheafifiedSingularCochains_isFlasque_of_open_paracompact
    (ModuleCat.of ℂ ℂ) X hpara n

/-- Metrizability discharges all the open-subspace hypotheses of the
genuine singular-cochain sheaf flasqueness theorem. -/
theorem sheafifiedSingularCochains_isFlasque_of_metrizable
    (A : ModuleCat.{0} R) (X : TopCat.{0}) [MetrizableSpace X] (n : ℕ) :
    TopCat.Sheaf.IsFlasque
      ((SheafQuasiIso.sheafifiedCochainComplex (DeRham.Comparison.SingularPresheaf.singularPresheafComplex A X)).X n) :=
  sheafifiedSingularCochains_isFlasque_of_open_paracompact A X
    (OpenParacompact.paracompactSpace_open_of_metrizable X) n

/-- On a finite-dimensional sigma-compact Hausdorff manifold, the actual
sheafified singular cochain complex is flasque in every degree. -/
theorem sheafifiedSingularCochains_isFlasque_of_chartedSpace
    (A : ModuleCat.{0} R) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (X : TopCat.{0}) [ChartedSpace E X]
    [SigmaCompactSpace X] [T2Space X] (n : ℕ) :
    TopCat.Sheaf.IsFlasque
      ((SheafQuasiIso.sheafifiedCochainComplex (DeRham.Comparison.SingularPresheaf.singularPresheafComplex A X)).X n) :=
  sheafifiedSingularCochains_isFlasque_of_open_paracompact A X
    (OpenParacompact.paracompactSpace_open_of_chartedSpace E X) n

/-- The installed complex-coefficient singular resolution is degreewise
flasque on the same actual manifolds. -/
theorem singularSheafComplex_X_isFlasque_of_chartedSpace
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (X : TopCat.{0}) [ChartedSpace E X] [SigmaCompactSpace X] [T2Space X] (n : ℕ) :
    TopCat.Sheaf.IsFlasque ((SheafResolution.singularSheafComplex X).X n) :=
  sheafifiedSingularCochains_isFlasque_of_chartedSpace (ModuleCat.of ℂ ℂ) E X n

end

end OAI.AlgebraicTopology.Cohomology.Singular.SheafFlasque
