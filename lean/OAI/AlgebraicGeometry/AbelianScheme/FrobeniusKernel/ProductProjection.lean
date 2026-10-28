import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierProducts
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EtaleOpen
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FiniteFlatCoverRetract
import OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelGroup

/-! # Product Projection -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ProductProjection.Construction

noncomputable section

/-! Removing the constant factor of a subgroup of M times E gives an
actual closed subgroup of M. Its open kernel still covers a singleton target. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelGroup.Construction

universe u

section General

variable {S : Scheme.{u}} {G M E : Grp (Over S)} (i : G ⟶ M ⊗ E)

abbrev productProjectionKernel : Grp (Over S) :=
  Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme (i ≫ AnnihilatorSheaf.Construction.splitSecondProjection M E).hom.hom)

def productProjectionKernelInclusion : productProjectionKernel i ⟶ G :=
  Grp.homMk (Picard.Homomorphisms.Kernel.Construction.kernelInclusion (i ≫ AnnihilatorSheaf.Construction.splitSecondProjection M E).hom.hom)

def productProjectionKernelFirst : productProjectionKernel i ⟶ M :=
  productProjectionKernelInclusion i ≫ i ≫ CartierProducts.Construction.splitFirstProjection M E

theorem productProjectionKernelFirst_inclusion :
    productProjectionKernelFirst i ≫ AnnihilatorSheaf.Construction.splitFirstInclusion M E = productProjectionKernelInclusion i ≫ i := by
  apply Grp.hom_ext
  change (Picard.Homomorphisms.Kernel.Construction.kernelInclusion (i ≫ AnnihilatorSheaf.Construction.splitSecondProjection M E).hom.hom ≫
      i.hom.hom ≫ fst M.X E.X) ≫ lift (𝟙 M.X) (1 : M.X ⟶ E.X) =
    Picard.Homomorphisms.Kernel.Construction.kernelInclusion (i ≫ AnnihilatorSheaf.Construction.splitSecondProjection M E).hom.hom ≫ i.hom.hom
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, lift_fst, Category.comp_id]
  · simp only [Category.assoc, lift_snd, MonObj.comp_one]
    exact (Picard.Homomorphisms.KernelGroup.Construction.kernelInclusion_comp (i ≫ AnnihilatorSheaf.Construction.splitSecondProjection M E).hom.hom).symm

theorem productProjectionKernelFirst_closed [IsSeparated E.X.hom]
    [IsClosedImmersion i.hom.hom.left] : IsClosedImmersion (productProjectionKernelFirst i).hom.hom.left := by
  have hc : IsClosedImmersion ((productProjectionKernelInclusion i).hom.hom.left ≫ i.hom.hom.left) :=
    inferInstanceAs (IsClosedImmersion
      ((Picard.Homomorphisms.Kernel.Construction.kernelInclusion (i ≫ AnnihilatorSheaf.Construction.splitSecondProjection M E).hom.hom).left ≫ i.hom.hom.left))
  have he : (productProjectionKernelFirst i).hom.hom.left ≫ (AnnihilatorSheaf.Construction.splitFirstInclusion M E).hom.hom.left =
      (productProjectionKernelInclusion i).hom.hom.left ≫ i.hom.hom.left :=
    congrArg (fun t : productProjectionKernel i ⟶ M ⊗ E => t.hom.hom.left)
      (productProjectionKernelFirst_inclusion i)
  have : IsClosedImmersion ((productProjectionKernelFirst i).hom.hom.left ≫
      (AnnihilatorSheaf.Construction.splitFirstInclusion M E).hom.hom.left) := (congrArg IsClosedImmersion he).mpr hc
  have : Mono (AnnihilatorSheaf.Construction.splitFirstInclusion M E).hom.hom := mono_of_mono_fac
    (show (AnnihilatorSheaf.Construction.splitFirstInclusion M E).hom.hom ≫ fst M.X E.X = 𝟙 M.X from lift_fst _ _)
  exact IsClosedImmersion.of_comp _ (AnnihilatorSheaf.Construction.splitFirstInclusion M E).hom.hom.left

end General

variable {k : Type u} [Field k] {G M J : Grp (Over (Spec (.of k)))}
  (D : Type u) [Group D] [Finite D]
  (i : G ⟶ M ⊗ EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of k)) D) (p : G ⟶ J)

theorem productEtaleKernelProjection_cover
    [IsFinite p.hom.hom.left] [Flat p.hom.hom.left] [LocallyOfFinitePresentation p.hom.hom.left]
    [Subsingleton J.X.left] :
    IsFinite (productProjectionKernelInclusion i ≫ p).hom.hom.left ∧
      Flat (productProjectionKernelInclusion i ≫ p).hom.hom.left ∧
      LocallyOfFinitePresentation (productProjectionKernelInclusion i ≫ p).hom.hom.left ∧
      Surjective (productProjectionKernelInclusion i ≫ p).hom.hom.left := by
  have : IsOpenImmersion (productProjectionKernelInclusion i).hom.hom.left :=
    EtaleOpen.Construction.kernelToEtale_inclusion_open (Spec (.of k)) D (i ≫ AnnihilatorSheaf.Construction.splitSecondProjection M _).hom.hom
  have : IsSeparated (EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of k)) D).X.hom := inferInstance
  have : IsClosedImmersion (productProjectionKernelInclusion i).hom.hom.left :=
    inferInstanceAs (IsClosedImmersion
      (Picard.Homomorphisms.Kernel.Construction.kernelInclusion (i ≫ AnnihilatorSheaf.Construction.splitSecondProjection M (EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of k)) D)).hom.hom).left)
  have : Nonempty (productProjectionKernel i).X.left :=
    ⟨η[(productProjectionKernel i).X].left (IsLocalRing.closedPoint k)⟩
  exact FiniteFlatCoverRetract.Construction.finite_flat_cover_of_open_closed_restriction
    (productProjectionKernelInclusion i).hom.hom.left p.hom.hom.left

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ProductProjection.Construction
