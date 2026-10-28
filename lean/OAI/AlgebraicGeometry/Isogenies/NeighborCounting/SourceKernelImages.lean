import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.FiniteFlatKernels
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GroupProductCoordinates

/-! # Source Kernel Images -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SourceKernelImages

noncomputable section

/-! The generic image formula survives transport into the actual
ambient source through its constructed integral product isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

section

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SubspaceCounts.Construction

universe u

variable {S : Scheme.{u}} {A B T M E : Over S}

def mapKernelPresentation (f : A ⟶ B) (K : Intrinsic.Neighbors.KernelPresentation A) : Intrinsic.Neighbors.KernelPresentation B :=
  ⟨K.carrier, K.inclusion ≫ f⟩

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V]
  [GrpObj A] [GrpObj M]
  (H : Submodule F V → Over S) (b : M ⊗ E ⟶ A) (e : ∀ U, H U ⟶ E)
  (χ : ∀ U : Submodule F V, (U →ₗ[F] F) → (H U ⟶ M))

omit [GrpObj A] [GrpObj M] in
theorem subspaceKernel_map (J : Submodule F (V × F)) :
    Intrinsic.Neighbors.subspaceKernel H b e χ J = mapKernelPresentation b (Intrinsic.Neighbors.subspaceKernel H (𝟙 (M ⊗ E)) e χ J) := by
  obtain ⟨⟨U, L | L⟩, rfl⟩ := (SubspaceCounts.Construction.allSubspacesEquiv (F := F) (V := V)).surjective J
  · rw [Intrinsic.Neighbors.subspaceKernel_equiv, Intrinsic.Neighbors.subspaceKernel_equiv]
    simp only [Intrinsic.Neighbors.kernelOfLiftData, mapKernelPresentation, QuotientGraphs.graphKernel, Category.comp_id]
  · rw [Intrinsic.Neighbors.subspaceKernel_equiv, Intrinsic.Neighbors.subspaceKernel_equiv]
    simp only [Intrinsic.Neighbors.kernelOfLiftData, mapKernelPresentation, QuotientGraphs.mixedKernel, Category.comp_id]

variable (s : M ⊗ E ≅ A) (m : (T ⟶ M) ≃ F) (v : (T ⟶ E) ≃ V)

def sourceKernelPointImage (K : Intrinsic.Neighbors.KernelPresentation A) : Set (V × F) :=
  Set.range (fun a : T ⟶ K.carrier => GenericParameters.blockCoordinates m v ((a ≫ K.inclusion) ≫ s.inv))

omit [Field F] [AddCommGroup V] [Module F V] [GrpObj A] [GrpObj M] in
theorem sourceKernelPointImage_map (K : Intrinsic.Neighbors.KernelPresentation (M ⊗ E)) :
    sourceKernelPointImage s m v (mapKernelPresentation s.hom K) = GenericParameters.kernelPointImage m v K := by
  unfold sourceKernelPointImage mapKernelPresentation GenericParameters.kernelPointImage
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

omit [GrpObj A] [GrpObj M] in
theorem source_subspace_kernel_image (J : Submodule F (V × F)) :
    sourceKernelPointImage s m v (Intrinsic.Neighbors.subspaceKernel H s.hom e χ J) =
      GenericParameters.kernelPointImage m v (Intrinsic.Neighbors.subspaceKernel H (𝟙 (M ⊗ E)) e χ J) := by
  rw [subspaceKernel_map, sourceKernelPointImage_map]

end

namespace Lifts

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SourceKernelImages

variable (R L : Type) [CommRing R] [IsDomain R] [ValuationRing R]
  [Field L] [Algebra R L] [IsFractionRing R L]
  {F V : Type} [Field F] [AddCommGroup V] [Module F V] [Finite V]
  {A M : Over (Spec (.of R))} [GrpObj A] [GrpObj M]
  [IsFinite M.hom] [Flat M.hom] [LocallyOfFinitePresentation M.hom]
  (m : (Evaluated.Sections.Lifts.genericTest R L ⟶ M) ≃* Multiplicative F)
  (s : M ⊗ (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) (Multiplicative V)).X ≅ A) [IsMonHom s.hom]

theorem evaluatedFiniteFlatKernel_generic_image (J : Submodule F (V × F)) :
    sourceKernelPointImage s (m.toEquiv.trans Multiplicative.toAdd)
      ((Evaluated.Characters.Lifts.genericConstantCoordinates R L (Multiplicative V)).toEquiv.trans Multiplicative.toAdd)
      (Evaluated.FiniteFlatKernels.Lifts.evaluatedFiniteFlatKernel R L m s J).toKernelPresentation = (J : Set (V × F)) := by
  rw [Evaluated.FiniteFlatKernels.Lifts.evaluatedFiniteFlatKernel_presentation, source_subspace_kernel_image]
  exact Evaluated.Characters.Lifts.evaluated_subspace_kernel_image R L M m J

end Lifts

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SourceKernelImages
