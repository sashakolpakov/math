import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SpecialKernelPresentations
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ResidueGraphSpecialization

/-! # Ordinary Coordinate Special Kernels -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting

noncomputable section

/-! The actual finite flat kernel of an ordinary coordinate model
specializes to the etale or mixed presentation prescribed by its
original subspace. Every graph character vanishes by Frobenius. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SpecialKernelPresentations OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SubspaceCounts.Construction
attribute [local instance] AbelianScheme.FrobeniusKernel.BaseChange.Construction.pulledBackGroup Classical.propDecidable

variable (R L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field L] [Algebra R L] [IsFractionRing R L] (q : ℕ) [Fact q.Prime]
  (A : Grp (Over (Spec (.of R)))) (C : OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel R L q A)

def OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.specialKernel
    (U : Submodule (ZMod q) (Fin 2 → ZMod q)) (flag : Bool) :
    Intrinsic.Neighbors.KernelPresentation
      ((Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).obj A.X) :=
  SpecialKernelPresentations.specialKernelPresentation
    (fun U : Submodule (ZMod q) (Fin 2 → ZMod q) =>
      (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) (Multiplicative U)).X)
    ((Grp.forget _).mapIso C.split).hom (Evaluated.Characters.Lifts.evaluatedEtaleInclusion R)
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) U flag

theorem OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.finiteFlatKernel_specialPresentation
    (ρ : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R)
    (J : Submodule (ZMod q) ((Fin 2 → ZMod q) × ZMod q)) :
    (C.finiteFlatKernel R L q A J).toKernelPresentation.pullback
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) =
      C.specialKernel R L q A (J.map (LinearMap.fst (ZMod q) (Fin 2 → ZMod q) (ZMod q)))
        (decide (SubspaceCounts.Construction.identityLine ≤ J)) := by
  let : IsFinite C.identity.X.hom := C.finite
  let : Flat C.identity.X.hom := C.flat
  let : LocallyOfFinitePresentation C.identity.X.hom := C.finitePresentation
  let e : C.identity.X ⊗
      (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) (Multiplicative (Fin 2 → ZMod q))).X ≅ A.X :=
    (Grp.forget _).mapIso C.split
  let : IsMonHom e.hom := C.split.hom.hom.isMonHom_hom
  change (Evaluated.FiniteFlatKernels.Lifts.evaluatedFiniteFlatKernel R L C.coordinates e J).toKernelPresentation.pullback
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) = _
  rw [Evaluated.FiniteFlatKernels.Lifts.evaluatedFiniteFlatKernel_presentation]
  exact SpecialKernelPresentations.subspaceKernel_specialPresentation _ e.hom (Evaluated.Characters.Lifts.evaluatedEtaleInclusion R)
    (Evaluated.Characters.Lifts.evaluatedGraphCharacter R L C.identity.X C.coordinates)
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))
    (fun U a => OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.character_specializes_zero_of_residueIso
      R L q A C ρ (Evaluated.Characters.Lifts.evaluatedGraphCharacter R L C.identity.X C.coordinates U a)) J

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting
