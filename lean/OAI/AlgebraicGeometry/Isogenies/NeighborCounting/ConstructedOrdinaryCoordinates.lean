import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GenericPointCoordinates
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PointRank
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OrdinaryComponentLift

/-! # Constructed Ordinary Coordinates -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ConstructedOrdinaryCoordinates.Lifts

noncomputable section

section

/-! Construct the ordinary component projection, integral product
splitting, and generic identity-line coordinate from the native ordinary
special fiber and one evaluated generic torsion scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OrdinaryComponentLift.Components
attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup
attribute [local instance] AbelianScheme.FrobeniusKernel.BaseChange.Construction.pulledBackGroup

theorem splitComponentProjection_surjective {S : Scheme} {A M E : Over S}
    [GrpObj A] [GrpObj M] [GrpObj E] (e : A ≅ M ⊗ E) [IsMonHom e.hom] :
    Surjective (SplitComponentKernel.Components.splitComponentProjection e).left := by
  let j : E ⟶ A := lift (1 : E ⟶ M) (𝟙 E) ≫ e.inv
  have hj : j ≫ SplitComponentKernel.Components.splitComponentProjection e = 𝟙 E := by
    simp only [j, SplitComponentKernel.Components.splitComponentProjection, Category.assoc, e.inv_hom_id_assoc, lift_snd]
  constructor
  intro y
  exact ⟨j.left y, congrArg (fun f : E.left ⟶ E.left ↦ f y) (congrArg Over.Hom.left hj)⟩

variable (R L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [Field L] [Algebra R L] [IsFractionRing R L]
variable (q : ℕ) [Fact q.Prime]
variable (A : Over (Spec (.of R))) [GrpObj A] [IsCommMonObj A]
  [IsFinite A.hom] [Flat A.hom]

variable {M : Over (Spec (.of (IsLocalRing.ResidueField R)))} [GrpObj M]
variable (e : (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).obj A ≅
  M ⊗ (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).obj
  (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) (Multiplicative (Fin 2 → ZMod q))).X) [IsMonHom e.hom]

omit [IsCommMonObj A] in
theorem constructedOrdinaryProjection_surjective : Surjective (OrdinaryComponentLift.Components.ordinaryComponentMap R e).left := by
  have : Surjective (SplitComponentKernel.Components.splitComponentProjection e).left := splitComponentProjection_surjective e
  exact (ComponentSurjective.Components.nativeComponentMap_geometry R (SplitComponentKernel.Components.splitComponentProjection e)).2.2.1

variable {I : Type} [Finite I]
variable (eA : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of L)) I ≅
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj A)
variable (hk : ∀ a : Evaluated.Sections.Lifts.genericTest R L ⟶ A, a ^ q = 1)
variable (hrank : A.hom.finrank
  (Spec.map (CommRingCat.ofHom (algebraMap R L)) (IsLocalRing.closedPoint L)) = q ^ 3)

include hrank eA in
omit [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R] [IsFractionRing R L]
  [Fact q.Prime] [GrpObj A] [IsCommMonObj A] in
theorem constructedOrdinary_generic_card : Nat.card (Evaluated.Sections.Lifts.genericTest R L ⟶ A) = q ^ 3 :=
  (Evaluated.PointRank.Lifts.evaluatedPoint_card_eq_rank R L A eA).trans hrank

def ordinaryIdentityCoordinates :
    (Evaluated.Sections.Lifts.genericTest R L ⟶ OrdinaryComponentLift.Components.ordinaryIdentityPart R e) ≃* Multiplicative (ZMod q) := by
  have : Surjective (OrdinaryComponentLift.Components.ordinaryComponentMap R e).left := constructedOrdinaryProjection_surjective R q A e
  exact GenericPointCoordinates.Lifts.constructedIdentityCoordinates R L q A hk
    (constructedOrdinary_generic_card R L q A eA hrank) (OrdinaryComponentLift.Components.ordinaryComponentMap R e) eA

/-- Unique extension of the derived generic linear section gives the
actual integral splitting of the source finite flat torsion block. -/
def ordinaryEvaluatedSplit : OrdinaryComponentLift.Components.ordinaryIdentityPart R e ⊗
    (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) (Multiplicative (Fin 2 → ZMod q))).X ≅ A := by
  letI := GenericPointCoordinates.Lifts.genericPointModule R L q A hk
  have : Surjective (OrdinaryComponentLift.Components.ordinaryComponentMap R e).left := constructedOrdinaryProjection_surjective R q A e
  exact GenericComponentSection.Lifts.splitEvaluatedComponent R L q (V := GenericPointCoordinates.Lifts.GenericPointSpace R L A) (W := Fin 2 → ZMod q)
    A (GenericPointCoordinates.Lifts.genericPointCoordinates R L A) (OrdinaryComponentLift.Components.ordinaryComponentMap R e)
    (Evaluated.ComponentSurjectivity.Lifts.evaluated_component_points_surjective R L (OrdinaryComponentLift.Components.ordinaryComponentMap R e) eA)

end

/-! The constructed integral ordinary product splitting preserves
the actual group law. This follows from the extended generic section
and the native split-extension group isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OrdinaryComponentLift.Components
attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup

section GenericSection

variable (R L : Type) [CommRing R] [IsDomain R] [ValuationRing R]
  [Field L] [Algebra R L] [IsFractionRing R L] (q : ℕ) [Fact q.Prime]
  {V W : Type} [AddCommGroup V] [Module (ZMod q) V] [AddCommGroup W] [Module (ZMod q) W]
  (A : Over (Spec (.of R))) [GrpObj A] [IsCommMonObj A] [IsProper A.hom] [Finite W]
  (c : (Evaluated.Sections.Lifts.genericTest R L ⟶ A) ≃* Multiplicative V)
  (π : A ⟶ (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) (Multiplicative W)).X) [IsMonHom π]
  (hπ : Function.Surjective (fun a : Evaluated.Sections.Lifts.genericTest R L ⟶ A => a ≫ π))

instance splitEvaluatedComponent_isMonHom : IsMonHom (GenericComponentSection.Lifts.splitEvaluatedComponent R L q A c π hπ).hom :=
  inferInstanceAs (IsMonHom (Evaluated.Splitting.Lifts.evaluatedComponentSplit R L A π
    (GenericComponentSection.Lifts.genericComponentSectionLabels R L q A c π hπ)
    (GenericComponentSection.Lifts.genericComponentSectionLabels_projection R L q A c π hπ)).hom)

end GenericSection

variable (R L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [Field L] [Algebra R L] [IsFractionRing R L]
  (q : ℕ) [Fact q.Prime] (A : Over (Spec (.of R))) [GrpObj A] [IsCommMonObj A]
  [IsFinite A.hom] [Flat A.hom]
  {M : Over (Spec (.of (IsLocalRing.ResidueField R)))} [GrpObj M]
  (e : (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).obj A ≅
    M ⊗ (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).obj
      (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) (Multiplicative (Fin 2 → ZMod q))).X) [IsMonHom e.hom]
  {I : Type} [Finite I]
  (eA : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of L)) I ≅
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj A)
  (hk : ∀ a : Evaluated.Sections.Lifts.genericTest R L ⟶ A, a ^ q = 1)

instance ordinaryEvaluatedSplit_isMonHom : IsMonHom (ordinaryEvaluatedSplit R L q A e eA hk).hom := by
  let := GenericPointCoordinates.Lifts.genericPointModule R L q A hk
  have : Surjective (OrdinaryComponentLift.Components.ordinaryComponentMap R e).left := constructedOrdinaryProjection_surjective R q A e
  exact splitEvaluatedComponent_isMonHom R L q
    (V := GenericPointCoordinates.Lifts.GenericPointSpace R L A) (W := Fin 2 → ZMod q) A (GenericPointCoordinates.Lifts.genericPointCoordinates R L A)
    (OrdinaryComponentLift.Components.ordinaryComponentMap R e) (Evaluated.ComponentSurjectivity.Lifts.evaluated_component_points_surjective R L (OrdinaryComponentLift.Components.ordinaryComponentMap R e) eA)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ConstructedOrdinaryCoordinates.Lifts
