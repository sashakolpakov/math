import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ComponentLift
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ComponentKernel
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Component Surjective -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ComponentSurjective.Components

noncomputable section

/-!
Surjectivity of the component map is proved from the special fiber.
The flat map has open image; the proper target over the local base
forces every nonempty closed complement to meet the closed fiber.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.Obj

universe u

variable (R : Type u) [CommRing R] [IsNoetherianRing R]
variable {A E : Over (Spec (.of R))}
variable [IsFinite A.hom] [Flat A.hom] [IsFinite E.hom] [Etale E.hom]

/-- A finite flat source maps onto the etale target if its native
special-fiber map is onto. No generic surjectivity is supplied. -/
theorem componentMap_surjective_of_special [IsLocalRing R] (f : A ⟶ E)
    (hf : Surjective
      ((Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).map f).left) :
    Surjective f.left := by
  let s := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  let F := Over.pullback s
  have : Flat f.left := ComponentKernel.Lifts.flat_map_to_etale f
  have : IsFinite f.left := ComponentKernel.Lifts.componentMap_finite f
  have : IsLocallyNoetherian E.left := LocallyOfFiniteType.isLocallyNoetherian E.hom
  have : LocallyOfFinitePresentation f.left := inferInstance
  have : Surjective (F.map f).left := hf
  constructor
  intro y
  by_contra hy
  have hclosed : IsClosed (E.hom '' (Set.range f.left)ᶜ) :=
    E.hom.isClosedMap _ f.left.isOpenMap.isOpen_range.isClosed_compl
  have hmem : IsLocalRing.closedPoint R ∈ E.hom '' (Set.range f.left)ᶜ :=
    (IsLocalRing.specializes_closedPoint (E.hom y)).mem_closed hclosed ⟨y, hy, rfl⟩
  obtain ⟨z, hz, hzs⟩ := hmem
  have hzrange : z ∈ Set.range (pullback.fst E.hom s) := by
    rw [Scheme.Pullback.range_fst]
    refine ⟨IsLocalRing.closedPoint (IsLocalRing.ResidueField R), ?_⟩
    change PrimeSpectrum.comap (IsLocalRing.residue R)
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField R)) = E.hom z
    rw [IsLocalRing.comap_closedPoint, hzs]
  obtain ⟨z₀, hz₀⟩ := hzrange
  obtain ⟨a₀, ha₀⟩ := (F.map f).left.surjective z₀
  have hp : (F.map f).left ≫ pullback.fst E.hom s =
      pullback.fst A.hom s ≫ f.left := pullback.lift_fst _ _ _
  apply hz
  refine ⟨pullback.fst A.hom s a₀, ?_⟩
  have he := congrArg (fun h => h a₀) hp
  change pullback.fst E.hom s ((F.map f).left a₀) =
    f.left (pullback.fst A.hom s a₀) at he
  exact he.symm.trans ((congrArg (pullback.fst E.hom s) ha₀).trans hz₀)

variable [HenselianLocalRing R] [GrpObj A] [GrpObj E]

/-- The constructed component projection is finite, flat, and onto,
as a consequence of the actual special-fiber projection. -/
theorem nativeComponentMap_geometry
    (π₀ : (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).obj A ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).obj E)
    [IsMonHom π₀] [Surjective π₀.left] :
    IsFinite (Intrinsic.ComponentLift.Components.nativeComponentMap R π₀).left ∧ Flat (Intrinsic.ComponentLift.Components.nativeComponentMap R π₀).left ∧
      Surjective (Intrinsic.ComponentLift.Components.nativeComponentMap R π₀).left ∧
      IsFinite (Picard.PoincareBundle.Kernel.Scheme.kernelObject (Intrinsic.ComponentLift.Components.nativeComponentMap R π₀)).hom ∧
      Flat (Picard.PoincareBundle.Kernel.Scheme.kernelObject (Intrinsic.ComponentLift.Components.nativeComponentMap R π₀)).hom := by
  refine ⟨ComponentKernel.Lifts.componentMap_finite _, ComponentKernel.Lifts.flat_map_to_etale _, ?_,
    ComponentKernel.Lifts.componentKernel_finite_flat _⟩
  apply componentMap_surjective_of_special R
  rw [Intrinsic.ComponentLift.Components.nativeComponentMap_special]
  infer_instance

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ComponentSurjective.Components
