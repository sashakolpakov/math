import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OrdinaryCoordinateSpecialKernels
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.Quotients
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.GroupPullbackComposition

/-! # Coordinate Special Kernels -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting

noncomputable section

/-! Transport the vanishing of the actual graph characters through the
given residue-field isomorphism. The resulting presentation lies on the
original geometric special fiber used by the PEL point comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.GroupPullbackComposition.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SubspaceCounts.Construction
attribute [local instance] AbelianScheme.FrobeniusKernel.BaseChange.Construction.pulledBackGroup Classical.propDecidable

theorem Geometric.CoordinateSpecialKernels.Lifts.pullback_comp_map_one {S T U : Scheme.{0}} (f : U ⟶ T) (g : T ⟶ S)
    {H M : Over S} [GrpObj M] (χ : H ⟶ M)
    (hχ : (Over.pullback g).map χ = 1) :
    (Over.pullback (f ≫ g)).map χ = 1 := by
  have heq : (Over.pullback (f ≫ g)).map χ =
      (Over.pullback (f ≫ g)).map (1 : H ⟶ M) := by
    apply (cancel_mono ((Over.pullbackComp f g).hom.app M)).mp
    rw [(Over.pullbackComp f g).hom.naturality χ,
      (Over.pullbackComp f g).hom.naturality (1 : H ⟶ M)]
    change (Over.pullbackComp f g).hom.app H ≫
      (Over.pullback f).map ((Over.pullback g).map χ) =
      (Over.pullbackComp f g).hom.app H ≫
        (Over.pullback f).map ((Over.pullback g).map (1 : H ⟶ M))
    rw [hχ, (Over.pullback g).map_one]
  exact heq.trans (Over.pullback (f ≫ g)).map_one

variable (R L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field L] [Algebra R L] [IsFractionRing R L] (q : ℕ) [Fact q.Prime]
  (A : Grp (Over (Spec (.of R)))) (C : OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel R L q A)
  (ρ : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R)

omit [IsFractionRing R L] in
theorem OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.character_geometric_specializes_zero
    {H : Over (Spec (.of R))} [Etale H.hom] (χ : H ⟶ C.identity.X) :
    (Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := ρ))).map χ = 1 :=
  Geometric.CoordinateSpecialKernels.Lifts.pullback_comp_map_one (Spec.map (CommRingCat.ofHom ρ.symm.toRingHom)) (Lifts.closedBase R) χ
    (OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.character_specializes_zero_of_residueIso R L q A C ρ χ)

def OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.geometricSpecialKernel
    (U : Submodule (ZMod q) (Fin 2 → ZMod q)) (flag : Bool) :
    Intrinsic.Neighbors.KernelPresentation ((Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := ρ))).obj A.X) :=
  SpecialKernelPresentations.specialKernelPresentation
    (fun U : Submodule (ZMod q) (Fin 2 → ZMod q) =>
      (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) (Multiplicative U)).X)
    ((Grp.forget _).mapIso C.split).hom (Evaluated.Characters.Lifts.evaluatedEtaleInclusion R)
    (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := ρ)) U flag

theorem OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.finiteFlatKernel_geometricSpecialPresentation
    (J : Submodule (ZMod q) ((Fin 2 → ZMod q) × ZMod q)) :
    (C.finiteFlatKernel R L q A J).toKernelPresentation.pullback
        (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := ρ)) =
      C.geometricSpecialKernel R L q A ρ
        (J.map (LinearMap.fst (ZMod q) (Fin 2 → ZMod q) (ZMod q)))
        (decide (SubspaceCounts.Construction.identityLine ≤ J)) := by
  let : IsFinite C.identity.X.hom := C.finite
  let : Flat C.identity.X.hom := C.flat
  let : LocallyOfFinitePresentation C.identity.X.hom := C.finitePresentation
  let e : C.identity.X ⊗
      (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) (Multiplicative (Fin 2 → ZMod q))).X ≅ A.X :=
    (Grp.forget _).mapIso C.split
  let : IsMonHom e.hom := C.split.hom.hom.isMonHom_hom
  change (Evaluated.FiniteFlatKernels.Lifts.evaluatedFiniteFlatKernel R L C.coordinates e J).toKernelPresentation.pullback
    (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := ρ)) = _
  rw [Evaluated.FiniteFlatKernels.Lifts.evaluatedFiniteFlatKernel_presentation]
  exact SpecialKernelPresentations.subspaceKernel_specialPresentation _ e.hom (Evaluated.Characters.Lifts.evaluatedEtaleInclusion R)
    (Evaluated.Characters.Lifts.evaluatedGraphCharacter R L C.identity.X C.coordinates)
    (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := ρ))
    (fun U a => OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.character_geometric_specializes_zero
      R L q A C ρ (Evaluated.Characters.Lifts.evaluatedGraphCharacter R L C.identity.X C.coordinates U a)) J

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting
