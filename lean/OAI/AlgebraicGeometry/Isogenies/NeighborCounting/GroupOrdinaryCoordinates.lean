import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ConstructedOrdinaryCoordinates

/-! # Group Ordinary Coordinates -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GroupOrdinaryCoordinates.Ordinary

noncomputable section

/-! Construct ordinary coordinates from the actual group-scheme
splitting, retaining its bundled group structures during specialization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ConstructedOrdinaryCoordinates.Lifts
attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup

variable (R L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [Field L] [Algebra R L] [IsFractionRing R L]
  (q : ℕ) [Fact q.Prime] (G : Grp (Over (Spec (.of R)))) [IsCommMonObj G.X]
  [IsFinite G.X.hom] [Flat G.X.hom]
  (M : Grp (Over (Spec (.of (IsLocalRing.ResidueField R)))))
  (e : (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).mapGrp.obj G ≅
    M ⊗ (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).mapGrp.obj
      (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) (Multiplicative (Fin 2 → ZMod q))))
  {I : Type} [Finite I]
  (eA : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of L)) I ≅
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj G.X)
  (hk : ∀ a : Evaluated.Sections.Lifts.genericTest R L ⟶ G.X, a ^ q = 1)
  (hrank : G.X.hom.finrank
    (Spec.map (CommRingCat.ofHom (algebraMap R L)) (IsLocalRing.closedPoint L)) = q ^ 3)

def groupOrdinaryIdentityCoordinates :=
  let eraw : (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).obj G.X ≅
      M.X ⊗ (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).obj
        (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) (Multiplicative (Fin 2 → ZMod q))).X :=
    (Grp.forget _).mapIso e
  letI : IsMonHom eraw.hom := e.hom.hom.isMonHom_hom
  ConstructedOrdinaryCoordinates.Lifts.ordinaryIdentityCoordinates (M := M.X) R L q G.X eraw eA hk hrank

def groupOrdinaryIntegralSplit :=
  let eraw : (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).obj G.X ≅
      M.X ⊗ (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).obj
        (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) (Multiplicative (Fin 2 → ZMod q))).X :=
    (Grp.forget _).mapIso e
  letI : IsMonHom eraw.hom := e.hom.hom.isMonHom_hom
  ConstructedOrdinaryCoordinates.Lifts.ordinaryEvaluatedSplit (M := M.X) R L q G.X eraw eA hk

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GroupOrdinaryCoordinates.Ordinary
