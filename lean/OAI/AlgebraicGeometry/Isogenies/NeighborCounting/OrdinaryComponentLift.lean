import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SplitComponentKernel
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ComponentSurjective
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.QuotientGraphs

/-! # Ordinary Component Lift -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OrdinaryComponentLift.Components

noncomputable section

/-!
Lift the ordinary special-fiber projection and identify its connected
kernel with the multiplicative special factor. Every integral character
from an etale group into this kernel specializes to zero, by Frobenius.
The projection, kernel, and their special-fiber comparisons are constructed.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup

variable (R : Type u) [CommRing R] [HenselianLocalRing R]
variable {A E : Over (Spec (.of R))} [GrpObj A] [GrpObj E]
variable [IsFinite A.hom] [IsFinite E.hom] [Etale E.hom]
variable {M : Over (Spec (.of (IsLocalRing.ResidueField R)))} [GrpObj M]
variable (e : (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).obj A ≅
  M ⊗ (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).obj E)
variable [IsMonHom e.hom]

def ordinaryComponentMap : A ⟶ E := Intrinsic.ComponentLift.Components.nativeComponentMap R (SplitComponentKernel.Components.splitComponentProjection e)

instance ordinaryComponentMap_isMonHom : IsMonHom (ordinaryComponentMap R e) :=
  inferInstanceAs (IsMonHom (Intrinsic.ComponentLift.Components.nativeComponentMap R (SplitComponentKernel.Components.splitComponentProjection e)))

abbrev ordinaryIdentityPart : Over (Spec (.of R)) := Picard.PoincareBundle.Kernel.Scheme.kernelObject (ordinaryComponentMap R e)

local instance ordinaryIdentityPart_group : GrpObj (ordinaryIdentityPart R e) :=
  Picard.PoincareBundle.Kernel.Scheme.kernelGroup (ordinaryComponentMap R e)

local instance ordinaryIdentityPart_special_group : GrpObj
    ((Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).obj
      (ordinaryIdentityPart R e)) :=
  Functor.grpObjObj (F := Over.pullback
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))

def ordinaryIdentitySpecialIso :
    (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).obj
      (ordinaryIdentityPart R e) ≅ M :=
  Kernel.SpecialFiber.Components.nativeComponentKernelSpecialIso R (SplitComponentKernel.Components.splitComponentProjection e) ≪≫ SplitComponentKernel.Components.splitComponentKernelIso e

instance ordinaryIdentitySpecialIso_isMonHom : IsMonHom (ordinaryIdentitySpecialIso R e).hom := by
  have : IsMonHom (Kernel.SpecialFiber.Components.nativeComponentKernelSpecialIso R (SplitComponentKernel.Components.splitComponentProjection e)).hom :=
    Kernel.SpecialFiber.Components.nativeComponentKernelSpecialIso_isMonHom R (SplitComponentKernel.Components.splitComponentProjection e)
  have : IsMonHom (SplitComponentKernel.Components.splitComponentKernelIso e).hom := SplitComponentKernel.Components.splitComponentKernelIso_isMonHom e
  change IsMonHom ((Kernel.SpecialFiber.Components.nativeComponentKernelSpecialIso R (SplitComponentKernel.Components.splitComponentProjection e)).hom ≫
    (SplitComponentKernel.Components.splitComponentKernelIso e).hom)
  infer_instance

omit [GrpObj A] [GrpObj M] [IsMonHom e.hom] in
theorem ordinaryIdentityPart_finite_flat [Flat A.hom] :
    IsFinite (ordinaryIdentityPart R e).hom ∧ Flat (ordinaryIdentityPart R e).hom :=
  ComponentKernel.Lifts.componentKernel_finite_flat (ordinaryComponentMap R e)

/-- Frobenius kills the lifted identity part's special fiber because
the actual ordinary multiplicative factor is killed by Frobenius. -/
theorem ordinaryIdentityPart_special_frobenius
    (q : ℕ) (hq : q.Prime)
    (hS : (q : Γ(Spec (.of (IsLocalRing.ResidueField R)), ⊤)) = 0)
    (hM : Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius q hq hS M = 1) :
    Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius q hq hS
      ((Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).obj
        (ordinaryIdentityPart R e)) = 1 := by
  let G := Over.pullback (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q hq _ hS)
  let i := ordinaryIdentitySpecialIso R e
  apply (cancel_mono (G.map i.hom)).mp
  have hn := (Picard.Homomorphisms.Group.Construction.relativeFrobeniusNat q hq hS).naturality i.hom
  change i.hom ≫ Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius q hq hS M =
    Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius q hq hS _ ≫ G.map i.hom at hn
  rw [hM, MonObj.comp_one] at hn
  exact hn.symm.trans (MonObj.one_comp (G.map i.hom)).symm

/-- Every constructed etale graph character specializes to the zero
map in the native identity component. -/
theorem ordinary_graph_character_specializes_to_zero
    (q : ℕ) (hq : q.Prime)
    (hS : (q : Γ(Spec (.of (IsLocalRing.ResidueField R)), ⊤)) = 0)
    [IsIso (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q hq _ hS)]
    (hM : Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius q hq hS M = 1)
    {H : Over (Spec (.of R))} [Etale H.hom] (χ : H ⟶ ordinaryIdentityPart R e) :
    (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).map χ = 1 := by
  have : Etale ((Over.pullback
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).obj H).hom := by
    dsimp
    infer_instance
  exact QuotientGraphs.etale_to_frobenius_killed q hq hS
    (ordinaryIdentityPart_special_frobenius R e q hq hS hM) _

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OrdinaryComponentLift.Components
