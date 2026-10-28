import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PairingRestriction
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SubgroupTransport

/-! # Pairing Iso Annihilator -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient

noncomputable section

/-! Annihilators transport through the actual group isomorphisms used
to identify native torsion after base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {A B U V W P : Over S}
  [GrpObj A] [GrpObj B] [GrpObj U] [GrpObj V] [GrpObj W]

theorem Annihilator.Construction.SchemeBicharacter.restrict_annihilator_iso
    (e : Annihilator.Construction.SchemeBicharacter (A := A) (B := B) (W := W))
    (f : U ⟶ A) [IsMonHom f] [IsIso f] (g : V ⟶ B) [IsMonHom g]
    (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) :
    (e.restrict f g).relativeAnnihilator (SubgroupTransport.Construction.relativeSubgroupPullback f F) =
      SubgroupTransport.Construction.relativeSubgroupPullback g (e.relativeAnnihilator F) := by
  ext T t y
  constructor
  · intro hy X k x hx
    have hpre : x ≫ inv f ∈ (SubgroupTransport.Construction.relativeSubgroupPullback f F).points X (k ≫ t) := by
      change (x ≫ inv f) ≫ f ∈ F.points X (k ≫ t)
      simpa only [Category.assoc, IsIso.inv_hom_id, Category.comp_id] using hx
    have hval := hy X k (x ≫ inv f) hpre
    change e.pairValue x (k ≫ (y ≫ g)) = 1
    simpa only [Annihilator.Construction.SchemeBicharacter.restrict_pairValue, Category.assoc, IsIso.inv_hom_id, Category.comp_id] using hval
  · intro hy X k x hx
    rw [Annihilator.Construction.SchemeBicharacter.restrict_pairValue, Category.assoc]
    exact hy X k (x ≫ f) hx

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient
