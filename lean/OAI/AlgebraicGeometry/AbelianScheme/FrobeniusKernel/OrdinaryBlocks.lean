import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EtaleSubgroups
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.AnnihilatorSheaf
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.Characters
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation

/-! # Ordinary Blocks -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction

noncomputable section

/-!
The ordinary block models are actual finite group schemes. The
multiplicative model is the spectrum of a group Hopf algebra, while the
étale model is the finite disjoint union with the same label group.
The ordinary splitting input is an isomorphism of these native schemes.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable (R : Type u) [CommRing R]

abbrev OrdinaryBlockLabels (q n d : ℕ) :=
  ULift.{u} (Multiplicative (Fin d → ZMod (q ^ n)))

/-- μ_(q^n)^d is defined by its actual coordinate Hopf algebra. -/
abbrev multiplicativeOrdinaryBlock (q n d : ℕ) :
    Grp (Over (Spec (.of R))) :=
  CartierDuality.Characters.Construction.affineHopfGroupScheme R (MonoidAlgebra R (OrdinaryBlockLabels.{u} q n d))

/-- The étale height-d block at level n. -/
def etaleOrdinaryBlock (q n d : ℕ) : Grp (Over (Spec (.of R))) :=
  EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) (OrdinaryBlockLabels.{u} q n d)

theorem multiplicativeOrdinaryBlock_finiteLocallyFree (q n d : ℕ) [NeZero q] :
    IsFinite (multiplicativeOrdinaryBlock R q n d).X.hom ∧
      Flat (multiplicativeOrdinaryBlock R q n d).X.hom ∧
      LocallyOfFinitePresentation (multiplicativeOrdinaryBlock R q n d).X.hom := by
  have : Finite (OrdinaryBlockLabels.{u} q n d) := inferInstance
  have : Module.FinitePresentation R (MonoidAlgebra R (OrdinaryBlockLabels.{u} q n d)) :=
    Module.finitePresentation_of_projective _ _
  change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R
      (MonoidAlgebra R (OrdinaryBlockLabels.{u} q n d))))) ∧
    Flat (Spec.map (CommRingCat.ofHom (algebraMap R
      (MonoidAlgebra R (OrdinaryBlockLabels.{u} q n d))))) ∧
    LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap R
      (MonoidAlgebra R (OrdinaryBlockLabels.{u} q n d)))))
  rw [IsFinite.SpecMap_iff, Flat.SpecMap_iff, LocallyOfFinitePresentation.SpecMap_iff]
  exact ⟨RingHom.finite_algebraMap.mpr inferInstance,
    RingHom.flat_algebraMap_iff.mpr inferInstance,
    RingHom.finitePresentation_algebraMap.mpr inferInstance⟩

theorem etaleOrdinaryBlock_finiteLocallyFree (q n d : ℕ) [NeZero q] :
    IsFinite (etaleOrdinaryBlock R q n d).X.hom ∧
      Flat (etaleOrdinaryBlock R q n d).X.hom ∧
      LocallyOfFinitePresentation (etaleOrdinaryBlock R q n d).X.hom := by
  have : Etale (etaleOrdinaryBlock R q n d).X.hom := EtaleSubgroups.Construction.etaleGroupScheme_etale _ _
  exact ⟨EtaleSubgroups.Construction.etaleGroupScheme_finite _ _, inferInstance, inferInstance⟩

/-- The assumed ordinary splitting, now in native finite group schemes.
For the active chosen block the heights are d=1 and r=2. The compact
blocks have heights (3,0) or (0,3). -/
abbrev OrdinaryBlockSplitting (B : Grp (Over (Spec (.of R)))) (q n d r : ℕ) :=
  B ≅ multiplicativeOrdinaryBlock R q n d ⊗ etaleOrdinaryBlock R q n r

/-- The chosen multiplicative subgroup in the original block coordinates. -/
def ordinaryMultiplicativeInclusion {B : Grp (Over (Spec (.of R)))}
    {q n d r : ℕ} (e : OrdinaryBlockSplitting R B q n d r) :
    multiplicativeOrdinaryBlock R q n d ⟶ B :=
  AnnihilatorSheaf.Construction.splitFirstInclusion (multiplicativeOrdinaryBlock R q n d) (etaleOrdinaryBlock R q n r) ≫ e.inv

/-- A finite subgroup with a monomorphic inclusion in a separated scheme
has an actual closed embedding. -/
theorem closedSubgroupOfFiniteMono {S : Scheme.{u}} {H B : Over S}
    (i : H ⟶ B) [Mono i] [IsFinite H.hom] [IsSeparated B.hom] :
    IsClosedImmersion i.left := by
  have : IsFinite (i.left ≫ B.hom) := (congrArg IsFinite i.w).mpr inferInstance
  have : IsFinite i.left := IsFinite.of_comp i.left B.hom
  exact (IsClosedImmersion.iff_isFinite_and_mono i.left).mpr ⟨inferInstance, inferInstance⟩

theorem splitFirstInclusion_closed {S : Scheme.{u}} (G H : Grp (Over S))
    [IsFinite G.X.hom] [IsFinite H.X.hom] :
    IsClosedImmersion (AnnihilatorSheaf.Construction.splitFirstInclusion G H).hom.hom.left := by
  have : Mono (AnnihilatorSheaf.Construction.splitFirstInclusion G H).hom.hom := mono_of_mono_fac
    (show (AnnihilatorSheaf.Construction.splitFirstInclusion G H).hom.hom ≫ fst G.X H.X = 𝟙 G.X from lift_fst _ _)
  have : IsSeparated (G ⊗ H).X.hom := by
    change IsSeparated (Limits.pullback.fst G.X.hom H.X.hom ≫ G.X.hom)
    infer_instance
  exact closedSubgroupOfFiniteMono (AnnihilatorSheaf.Construction.splitFirstInclusion G H).hom.hom

theorem splitSecondInclusion_closed {S : Scheme.{u}} (G H : Grp (Over S))
    [IsFinite G.X.hom] [IsFinite H.X.hom] :
    IsClosedImmersion (AnnihilatorSheaf.Construction.splitSecondInclusion G H).hom.hom.left := by
  have : Mono (AnnihilatorSheaf.Construction.splitSecondInclusion G H).hom.hom := mono_of_mono_fac
    (show (AnnihilatorSheaf.Construction.splitSecondInclusion G H).hom.hom ≫ snd G.X H.X = 𝟙 H.X from lift_snd _ _)
  have : IsSeparated (G ⊗ H).X.hom := by
    change IsSeparated (Limits.pullback.fst G.X.hom H.X.hom ≫ G.X.hom)
    infer_instance
  exact closedSubgroupOfFiniteMono (AnnihilatorSheaf.Construction.splitSecondInclusion G H).hom.hom

/-- The multiplicative part of an ordinary block is a finite locally free
closed subgroup of that block, constructed in its original coordinates. -/
theorem ordinaryMultiplicativeInclusion_closed {B : Grp (Over (Spec (.of R)))}
    {q n d r : ℕ} [NeZero q] (e : OrdinaryBlockSplitting R B q n d r) :
    IsClosedImmersion (ordinaryMultiplicativeInclusion R e).hom.hom.left := by
  have : IsFinite (multiplicativeOrdinaryBlock R q n d).X.hom :=
    (multiplicativeOrdinaryBlock_finiteLocallyFree R q n d).1
  have : IsFinite (etaleOrdinaryBlock R q n r).X.hom :=
    (etaleOrdinaryBlock_finiteLocallyFree R q n r).1
  have : IsClosedImmersion
      (AnnihilatorSheaf.Construction.splitFirstInclusion (multiplicativeOrdinaryBlock R q n d)
        (etaleOrdinaryBlock R q n r)).hom.hom.left := splitFirstInclusion_closed _ _
  have : IsIso e.inv.hom.hom.left := inferInstanceAs
    (IsIso (((Grp.forget (Over (Spec (.of R)))) ⋙ Over.forget _).map e.inv))
  change IsClosedImmersion
    ((AnnihilatorSheaf.Construction.splitFirstInclusion (multiplicativeOrdinaryBlock R q n d)
      (etaleOrdinaryBlock R q n r)).hom.hom.left ≫ e.inv.hom.hom.left)
  infer_instance

/-- Under CartierDuality's polarization identification of the opposite block with
characters, the annihilator of the chosen multiplicative kernel is the
dual étale block. The calculation is made in the original block scheme. -/
def ordinaryMultiplicativeAnnihilatorIso {B : Grp (Over (Spec (.of R)))}
    {q n d r : ℕ} (e : OrdinaryBlockSplitting R B q n d r) :
    CartierDuality.CharacterSheaf.Construction.Schemes.annihilatorSheaf (ordinaryMultiplicativeInclusion R e) ≅
      CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf (Spec (.of R)) (etaleOrdinaryBlock R q n r) :=
  AnnihilatorSheaf.Construction.annihilatorSheafIsoOfSplitting B (multiplicativeOrdinaryBlock R q n d)
    (etaleOrdinaryBlock R q n r) e

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction
