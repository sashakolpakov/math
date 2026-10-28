import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ConstructedOrdinaryCoordinates
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GroupProductCoordinates
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.FiniteFlatKernels
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.StandardResidueSplitting

/-! # Ordinary Coordinate Linear -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OrdinaryCoordinateLinear.Lifts

noncomputable section

/-! Package the constructed integral ordinary product, its actual
multiplicative special fiber, and the generic identity-line coordinates.
The package retains the original ambient group scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GroupProductCoordinates
attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup

variable (R L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field L] [Algebra R L]
  (q : ℕ) [Fact q.Prime] (A : Grp (Over (Spec (.of R))))

structure OrdinaryCoordinateModel where
  identity : Grp (Over (Spec (.of R)))
  finite : IsFinite identity.X.hom
  flat : Flat identity.X.hom
  finitePresentation : LocallyOfFinitePresentation identity.X.hom
  special : (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).mapGrp.obj identity ≅
    AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock (IsLocalRing.ResidueField R) q 1 1
  split : identity ⊗ AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) (Multiplicative (Fin 2 → ZMod q)) ≅ A
  coordinates : (Evaluated.Sections.Lifts.genericTest R L ⟶ identity.X) ≃* Multiplicative (ZMod q)

variable [HenselianLocalRing R]
  [IsFractionRing R L] [IsCommMonObj A.X] [IsFinite A.X.hom] [Flat A.X.hom]
  (e : (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).mapGrp.obj A ≅
    AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock (IsLocalRing.ResidueField R) q 1 1 ⊗
      (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).mapGrp.obj
        (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) (Multiplicative (Fin 2 → ZMod q))))
  {I : Type} [Finite I]
  (eA : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of L)) I ≅
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj A.X)
  (hk : ∀ a : Evaluated.Sections.Lifts.genericTest R L ⟶ A.X, a ^ q = 1)
  (hrank : A.X.hom.finrank
    (Spec.map (CommRingCat.ofHom (algebraMap R L)) (IsLocalRing.closedPoint L)) = q ^ 3)

def constructOrdinaryCoordinateModel : OrdinaryCoordinateModel R L q A := by
  let eraw : (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).obj A.X ≅
      (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock (IsLocalRing.ResidueField R) q 1 1).X ⊗
        (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).obj
          (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) (Multiplicative (Fin 2 → ZMod q))).X :=
    (Grp.forget _).mapIso e
  letI : IsMonHom eraw.hom := e.hom.hom.isMonHom_hom
  exact {
    identity := Grp.mk (OrdinaryComponentLift.Components.ordinaryIdentityPart R eraw)
    finite := (OrdinaryComponentLift.Components.ordinaryIdentityPart_finite_flat R eraw).1
    flat := (OrdinaryComponentLift.Components.ordinaryIdentityPart_finite_flat R eraw).2
    finitePresentation := ComponentKernel.Lifts.componentKernel_finitePresentation (OrdinaryComponentLift.Components.ordinaryComponentMap R eraw)
    special := Grp.mkIso' (OrdinaryComponentLift.Components.ordinaryIdentitySpecialIso R eraw)
    split := Grp.mkIso' (ConstructedOrdinaryCoordinates.Lifts.ordinaryEvaluatedSplit R L q A.X eraw eA hk)
    coordinates := ConstructedOrdinaryCoordinates.Lifts.ordinaryIdentityCoordinates R L q A.X eraw eA hk hrank }

def OrdinaryCoordinateModel.linearCoordinates (C : OrdinaryCoordinateModel R L q A)
    (hk : ∀ a : Evaluated.Sections.Lifts.genericTest R L ⟶ A.X, a ^ q = 1) :=
  letI := GenericPointCoordinates.Lifts.genericPointModule R L q A.X hk
  let eraw : C.identity.X ⊗
      (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) (Multiplicative (Fin 2 → ZMod q))).X ≅ A.X :=
    (Grp.forget _).mapIso C.split
  letI : IsMonHom eraw.hom := C.split.hom.hom.isMonHom_hom
  GroupProductCoordinates.sourceProductPointLinearEquiv q C.coordinates
    (Evaluated.Characters.Lifts.genericConstantCoordinates R L (Multiplicative (Fin 2 → ZMod q))) eraw

def OrdinaryCoordinateModel.finiteFlatKernel (C : OrdinaryCoordinateModel R L q A)
    (J : Submodule (ZMod q) ((Fin 2 → ZMod q) × ZMod q)) : Kernel.Properties.FiniteFlatKernel A.X :=
  letI : IsFinite C.identity.X.hom := C.finite
  letI : Flat C.identity.X.hom := C.flat
  letI : LocallyOfFinitePresentation C.identity.X.hom := C.finitePresentation
  let eraw : C.identity.X ⊗
      (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) (Multiplicative (Fin 2 → ZMod q))).X ≅ A.X :=
    (Grp.forget _).mapIso C.split
  letI : IsMonHom eraw.hom := C.split.hom.hom.isMonHom_hom
  Evaluated.FiniteFlatKernels.Lifts.evaluatedFiniteFlatKernel R L C.coordinates eraw J

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OrdinaryCoordinateLinear.Lifts
