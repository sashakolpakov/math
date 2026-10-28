import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CartierPairing
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OppositeCartierComparison
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CompactOpposites
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PairingIsoAnnihilator

/-! # Cartier Nondegeneracy -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CartierNondegeneracy

noncomputable section

/-! The actual Cartier evaluation pairing has trivial annihilator of
the whole chosen group. This property transports through the original
opposite identification and the native coefficient-block isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CompactOpposites.Kernel OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CartierPairing OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OppositeCartierComparison

section Cartier

variable {R : CommRingCat.{u}} {G : Grp (Over (Spec R))} {X : Over (Spec R)}
variable (P : AbelianScheme.FrobeniusKernel.CartierModel.Construction.CartierCoordinates R G)

local instance : IsCommMonObj P.dualGroup.X := P.dualGroup_commutative

theorem cartier_annihilator_whole :
    (CartierPairing.cartierPairing P).relativeAnnihilator (CompactOpposites.Kernel.wholeRelativeSubgroup G.X X) =
      AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.trivialRelativeSubgroup (A := P.dualGroup.X) (P := X) := by
  ext T t b
  constructor
  · intro hb
    have hc : P.pointsEquiv T b = 1 := by
      apply (CartierPairing.character_eq_one_iff T (P.pointsEquiv T b)).mpr
      intro U f a
      have h := hb U f a (Subgroup.mem_top a)
      rw [CartierPairing.cartierPairing_pairValue, CartierPairing.cartierPairValue, CartierPairing.pointCharacters_natural] at h
      exact h
    change b = 1
    exact (P.pointsEquiv T).injective (hc.trans (P.pointsEquiv T).map_one.symm)
  · intro hb
    change b = 1 at hb
    subst b
    intro U f a _
    change (CartierPairing.cartierPairing P).pairValue a (f ≫ 1) = 1
    rw [MonObj.comp_one]
    exact (CartierPairing.cartierPairing P).one_right U a

end Cartier

section Transport

variable {S : Scheme.{u}} {A B U V W X : Over S}
variable [GrpObj A] [GrpObj B] [GrpObj U] [GrpObj V] [GrpObj W]
variable [IsCommMonObj B] [IsCommMonObj V]

theorem restricted_annihilator_whole
    (e : AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter (A := A) (B := B) (W := W))
    (a : U ≅ A) (b : V ≅ B) [IsMonHom a.hom] [IsMonHom b.hom]
    (he : e.relativeAnnihilator (CompactOpposites.Kernel.wholeRelativeSubgroup A X) =
      AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.trivialRelativeSubgroup (A := B) (P := X)) :
    (e.restrict a.hom b.hom).relativeAnnihilator (CompactOpposites.Kernel.wholeRelativeSubgroup U X) =
      AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.trivialRelativeSubgroup (A := V) (P := X) := by
  have hwhole : AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback a.hom (CompactOpposites.Kernel.wholeRelativeSubgroup A X) = CompactOpposites.Kernel.wholeRelativeSubgroup U X := by
    ext T t x
    exact Iff.rfl
  rw [← hwhole, AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter.restrict_annihilator_iso, he, CompactOpposites.Kernel.pullback_trivial]

theorem zero_double_annihilator_of_whole
    (e : AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter (A := A) (B := B) (W := W))
    (he : e.relativeAnnihilator (CompactOpposites.Kernel.wholeRelativeSubgroup A X) =
      AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.trivialRelativeSubgroup (A := B) (P := X)) :
    e.relativeAnnihilator (e.flip.relativeAnnihilator (AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.trivialRelativeSubgroup (A := B) (P := X))) =
      AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.trivialRelativeSubgroup (A := B) (P := X) := by
  rw [CompactOpposites.Kernel.annihilator_trivial e.flip, he]

end Transport

variable {K : Type u} [Field K]
variable {G B : Grp (Over (Spec (.of K)))} [IsCommMonObj B.X]
variable {U V X : Over (Spec (.of K))} [GrpObj U] [GrpObj V] [IsCommMonObj V]
variable (P : AbelianScheme.FrobeniusKernel.CartierModel.Construction.CartierCoordinates (.of K) G) (d : B ≅ P.dualGroup)

local instance : IsCommMonObj P.dualGroup.X := P.dualGroup_commutative

theorem opposite_annihilator_whole :
    (OppositeCartierComparison.oppositePairing P d).relativeAnnihilator (CompactOpposites.Kernel.wholeRelativeSubgroup G.X X) =
      AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.trivialRelativeSubgroup (A := B.X) (P := X) :=
  @restricted_annihilator_whole (Spec (.of K)) G.X P.dualGroup.X G.X B.X
    (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of K))).X X
    (inferInstanceAs (GrpObj G.X)) (inferInstanceAs (GrpObj P.dualGroup.X))
    (inferInstanceAs (GrpObj G.X)) (inferInstanceAs (GrpObj B.X))
    (inferInstanceAs (GrpObj (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of K))).X))
    P.dualGroup_commutative inferInstance
    (CartierPairing.cartierPairing P) (Iso.refl G.X) ((Grp.forget _).mapIso d)
    (inferInstanceAs (IsMonHom (𝟙 G.X))) (inferInstanceAs (IsMonHom d.hom.hom.hom))
    (cartier_annihilator_whole P)

theorem coefficient_annihilator_zero_double (a : U ≅ G.X) (b : V ≅ B.X)
    [IsMonHom a.hom] [IsMonHom b.hom] :
    ((OppositeCartierComparison.oppositePairing P d).restrict a.hom b.hom).relativeAnnihilator
      (((OppositeCartierComparison.oppositePairing P d).restrict a.hom b.hom).flip.relativeAnnihilator
        (AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.trivialRelativeSubgroup (A := V) (P := X))) =
      AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.trivialRelativeSubgroup (A := V) (P := X) :=
  zero_double_annihilator_of_whole _
    (restricted_annihilator_whole (OppositeCartierComparison.oppositePairing P d) a b (opposite_annihilator_whole P d))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CartierNondegeneracy
