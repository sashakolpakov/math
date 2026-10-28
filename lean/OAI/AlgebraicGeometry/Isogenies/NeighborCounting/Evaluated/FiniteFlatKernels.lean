import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.Characters
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Properties
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EtaleSubgroups

/-! # Finite Flat Kernels -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.FiniteFlatKernels.Lifts

noncomputable section

/-! Each evaluated active subspace constructs a finite flat closed
integral subgroup from its graph or mixed product presentation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Properties

variable (R L : Type) [CommRing R] [IsDomain R] [ValuationRing R]
  [Field L] [Algebra R L] [IsFractionRing R L]
  {F V : Type} [Field F] [AddCommGroup V] [Module F V] [Finite V]

instance evaluatedEtaleInclusion_isMonHom (U : Submodule F V) :
    IsMonHom (Characters.Lifts.evaluatedEtaleInclusion R U) :=
  (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupMap (Spec (.of R)) U.subtype.toAddMonoidHom.toMultiplicative).hom.isMonHom_hom

instance evaluatedEtaleInclusion_closed (U : Submodule F V) :
    IsClosedImmersion (Characters.Lifts.evaluatedEtaleInclusion R U).left :=
  AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupMap_closed (Spec (.of R)) U.subtype.toAddMonoidHom.toMultiplicative
    (fun _a _b h => Multiplicative.toAdd.injective (Subtype.ext (congrArg Multiplicative.toAdd h)))

variable {A M : Over (Spec (.of R))} [GrpObj A] [GrpObj M]
  [IsFinite M.hom] [Flat M.hom] [LocallyOfFinitePresentation M.hom]
  (m : (Sections.Lifts.genericTest R L ⟶ M) ≃* Multiplicative F)
  (e : M ⊗ (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) (Multiplicative V)).X ≅ A)
  [IsMonHom e.hom]

/-- The required geometry of every constructed integral active kernel. -/
theorem evaluated_subspace_is_finiteFlat (J : Submodule F (V × F)) :
    ∃ K : Kernel.Properties.FiniteFlatKernel A, K.toKernelPresentation =
      Intrinsic.Neighbors.subspaceKernel (fun U : Submodule F V =>
        (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) (Multiplicative U)).X)
        e.hom (Characters.Lifts.evaluatedEtaleInclusion R) (Characters.Lifts.evaluatedGraphCharacter R L M m) J := by
  have : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  exact Kernel.Properties.subspaceKernel_is_finiteFlat _ e.hom (Characters.Lifts.evaluatedEtaleInclusion R)
    (Characters.Lifts.evaluatedGraphCharacter R L M m) J

def evaluatedFiniteFlatKernel (J : Submodule F (V × F)) : Kernel.Properties.FiniteFlatKernel A :=
  Classical.choose (evaluated_subspace_is_finiteFlat R L m e J)

theorem evaluatedFiniteFlatKernel_presentation (J : Submodule F (V × F)) :
    (evaluatedFiniteFlatKernel R L m e J).toKernelPresentation =
      Intrinsic.Neighbors.subspaceKernel (fun U : Submodule F V =>
        (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) (Multiplicative U)).X)
        e.hom (Characters.Lifts.evaluatedEtaleInclusion R) (Characters.Lifts.evaluatedGraphCharacter R L M m) J :=
  Classical.choose_spec (evaluated_subspace_is_finiteFlat R L m e J)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.FiniteFlatKernels.Lifts
