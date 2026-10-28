import OAI.AlgebraicTopology.Cohomology.Singular.SupportedRelativeMap
import OAI.AlgebraicTopology.Cohomology.Singular.RelativeOpenKernel
import OAI.AlgebraicTopology.Cohomology.Singular.SheafFlasque
import OAI.AlgebraicTopology.Cohomology.Singular.ShortExactQuasiIso

/-! # Supported Relative Comparison -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison

noncomputable section

section

/-!
# Actual relative cochains and supported singular-sheaf sections

The genuine open-section sheafification units give a map between the kernels
of restriction to an open complement. The two kernel sequences are short
exact, so the proved first-term five lemma gives a quasi-isomorphism whenever
the absolute and open-complement unit maps are quasi-isomorphisms. The source
kernel is identified with the existing actual relative singular cochains.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace
open scoped _root_.Manifold

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section ComparisonMaps

variable {R : Type} [Ring R] (M : ModuleCat.{0} R) (X : TopCat.{0}) (O U : Opens X)

/-- Surjectivity of actual sheaf-section restriction makes the target
kernel sequence short exact. Only the smaller open set is used here. -/
theorem supportedSingularSheafKernelSequence_shortExact
    [ParacompactSpace (U ⊓ O : Opens X)] [T2Space (U ⊓ O : Opens X)] :
    (SurjectiveQuasiIso.cochainKernelSequence (OpenSheafComparison.singularSheafSectionsRestriction M X
      (homOfLE (inf_le_left : U ⊓ O ≤ U)))).ShortExact := by
  have := SheafFlasque.singularSheafSectionsRestriction_epi_of_paracompact M X
    (homOfLE (inf_le_left : U ⊓ O ≤ U))
  change (ShortComplex.mk (kernel.ι _) _ _).ShortExact
  exact { exact := ShortComplex.kernelSequence_exact _ }

end ComparisonMaps

variable (F : Type) [Field F] [CharZero F] (X : TopCat.{0}) (O U : Opens X)

/-- The true absolute and open-complement comparisons imply a
quasi-isomorphism on the actual kernels, by the short-exact-sequence theorem. -/
theorem quasiIso_openSupportedSingularKernelComparison_of_paracompact
    [ParacompactSpace U] [T2Space U]
    [ParacompactSpace (U ⊓ O : Opens X)] [T2Space (U ⊓ O : Opens X)] :
    QuasiIso (SupportedRelativeMap.openSupportedSingularKernelComparison (ModuleCat.of F F) X O U) :=
  ShortExactQuasiIso.quasiIso_first_of_shortExact
    (SupportedRelativeMap.openSupportedKernelSequenceMap (ModuleCat.of F F) X O U)
    (RelativeOpenKernel.openSupportKernelSequence_shortExact X (ModuleCat.of F F) O U)
    (supportedSingularSheafKernelSequence_shortExact (ModuleCat.of F F) X O U)
    (OpenSheafComparison.quasiIso_singularCochainsToOpenSheafSections_of_paracompact F X U)
    (OpenSheafComparison.quasiIso_singularCochainsToOpenSheafSections_of_paracompact F X (U ⊓ O))

/-- The kernel-source comparison into actual supported sheaf sections
is a quasi-isomorphism under the same two open-subspace hypotheses. -/
theorem quasiIso_openSupportedSingularComparison_of_paracompact
    [ParacompactSpace U] [T2Space U]
    [ParacompactSpace (U ⊓ O : Opens X)] [T2Space (U ⊓ O : Opens X)] :
    QuasiIso (SupportedRelativeMap.openSupportedSingularComparison (ModuleCat.of F F) X O U) := by
  have := quasiIso_openSupportedSingularKernelComparison_of_paracompact F X O U
  unfold SupportedRelativeMap.openSupportedSingularComparison
  infer_instance

/-- Genuine relative singular cochains compute the sections of the
supported singular sheaf complex through the canonical comparison map. -/
theorem quasiIso_relativeToSupportedSheafSections_of_paracompact
    [ParacompactSpace U] [T2Space U]
    [ParacompactSpace (U ⊓ O : Opens X)] [T2Space (U ⊓ O : Opens X)] :
    QuasiIso (SupportedRelativeMap.relativeToSupportedSheafSections (ModuleCat.of F F) X O U) := by
  have := quasiIso_openSupportedSingularComparison_of_paracompact F X O U
  unfold SupportedRelativeMap.relativeToSupportedSheafSections
  infer_instance

/-- Metrizability supplies both required open-subspace hypotheses. -/
theorem quasiIso_relativeToSupportedSheafSections_of_metrizable
    [MetrizableSpace X] :
    QuasiIso (SupportedRelativeMap.relativeToSupportedSheafSections (ModuleCat.of F F) X O U) := by
  have := OpenParacompact.paracompactSpace_open_of_metrizable X U
  have := OpenParacompact.paracompactSpace_open_of_metrizable X (U ⊓ O)
  exact quasiIso_relativeToSupportedSheafSections_of_paracompact F X O U

/-- Finite-dimensional sigma-compact Hausdorff charted spaces satisfy the
comparison hypotheses by the proved topology of their open subspaces. -/
theorem quasiIso_relativeToSupportedSheafSections_of_chartedSpace
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [ChartedSpace E X] [SigmaCompactSpace X] [T2Space X] :
    QuasiIso (SupportedRelativeMap.relativeToSupportedSheafSections (ModuleCat.of F F) X O U) := by
  have := OpenParacompact.paracompactSpace_open_of_chartedSpace E X U
  have := OpenParacompact.paracompactSpace_open_of_chartedSpace E X (U ⊓ O)
  exact quasiIso_relativeToSupportedSheafSections_of_paracompact F X O U

end

/-!
# Global relative cochains and global supported-sheaf sections

The actual top-open identification of pairs converts the verified open-set
comparison to a map whose source is the original relative singular cochain
complex on `X`. Its inclusion is the genuine global sheafification unit.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open scoped _root_.Manifold

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section GlobalMap

variable {R : Type} [Ring R] (M : ModuleCat.{0} R) (X : TopCat.{0}) (O : Opens X)

/-- The canonical comparison has the actual original-space relative
cochain complex as its source. -/
def relativeToSupportedSheafGlobalSections :
    RelativeSequence.relativeSingularCochains M X (O : Set X) ⟶
      AlgebraicGeometry.CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafSections M X O ⊤ :=
  (RelativeOpenSupport.relativeCochainPresheafTopIso M X (O : Set X)).inv ≫
    SupportedRelativeMap.relativeToSupportedSheafSections M X O ⊤

/-- Forgetting support after the global relative comparison is exactly
the original-space relative inclusion followed by the global unit. -/
@[reassoc (attr := simp)]
theorem relativeToSupportedSheafGlobalSections_inclusion :
    relativeToSupportedSheafGlobalSections M X O ≫
        AlgebraicGeometry.CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafSectionsInclusion M X O ⊤ =
      RelativeSequence.relativeCochainInclusion M X (O : Set X) ≫ LocallyZeroCochains.singularCochainsToSheafSections M X := by
  rw [relativeToSupportedSheafGlobalSections, Category.assoc,
    SupportedRelativeMap.relativeToSupportedSheafSections_inclusion, ← Category.assoc]
  change (RelativeSequence.relativeSingularCochainsMap M (Opens.inclusionTopIso X).hom
      (A := RelativeOpenSupport.relativeOpenSubspace (O : Set X) (⊤ : Opens X)) (B := (O : Set X))
      (fun _ hx => hx) ≫
        RelativeSequence.relativeCochainInclusion M (TopCat.of (⊤ : Opens X))
          (RelativeOpenSupport.relativeOpenSubspace (O : Set X) (⊤ : Opens X))) ≫
      OpenSheafComparison.singularCochainsToOpenSheafSections M X ⊤ = _
  have h := RelativeSequence.relativeCochainInclusion_naturality M
    (X := TopCat.of (⊤ : Opens X)) (Y := X) (Opens.inclusionTopIso X).hom
    (A := RelativeOpenSupport.relativeOpenSubspace (O : Set X) (⊤ : Opens X)) (B := (O : Set X))
    (fun _ hx => hx)
  exact (congrArg (fun f => f ≫ OpenSheafComparison.singularCochainsToOpenSheafSections M X ⊤) h).trans
    (Category.assoc _ _ _)

end GlobalMap

variable (F : Type) [Field F] [CharZero F] (X : TopCat.{0}) (O : Opens X)

/-- Paracompactness of `X` and the actual open complement suffices for
the canonical global relative-to-supported comparison. -/
theorem quasiIso_relativeToSupportedSheafGlobalSections_of_paracompact
    [ParacompactSpace X] [T2Space X] [ParacompactSpace O] :
    QuasiIso (relativeToSupportedSheafGlobalSections (ModuleCat.of F F) X O) := by
  have : ParacompactSpace (⊤ : Opens X) :=
    (TopCat.homeoOfIso (Opens.inclusionTopIso X)).paracompactSpace_iff.mpr inferInstance
  have : ParacompactSpace ((⊤ : Opens X) ⊓ O : Opens X) := by
    exact (top_inf_eq O).symm ▸ (inferInstance : ParacompactSpace O)
  have := quasiIso_relativeToSupportedSheafSections_of_paracompact F X O ⊤
  unfold relativeToSupportedSheafGlobalSections
  infer_instance

/-- A metrizable ambient space supplies all the needed open-subspace
topology for the global comparison. -/
theorem quasiIso_relativeToSupportedSheafGlobalSections_of_metrizable
    [MetrizableSpace X] :
    QuasiIso (relativeToSupportedSheafGlobalSections (ModuleCat.of F F) X O) := by
  have := quasiIso_relativeToSupportedSheafSections_of_metrizable F X O ⊤
  unfold relativeToSupportedSheafGlobalSections
  infer_instance

/-- The actual global comparison on finite-dimensional sigma-compact
Hausdorff charted spaces. -/
theorem quasiIso_relativeToSupportedSheafGlobalSections_of_chartedSpace
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [ChartedSpace E X] [SigmaCompactSpace X] [T2Space X] :
    QuasiIso (relativeToSupportedSheafGlobalSections (ModuleCat.of F F) X O) := by
  have := quasiIso_relativeToSupportedSheafSections_of_chartedSpace F X O ⊤ E
  unfold relativeToSupportedSheafGlobalSections
  infer_instance

end

end OAI.AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison
