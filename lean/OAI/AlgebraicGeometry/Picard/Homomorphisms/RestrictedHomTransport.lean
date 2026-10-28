import OAI.AlgebraicGeometry.Picard.Homomorphisms.OpenPullbackCoherence
import OAI.AlgebraicGeometry.Picard.Homomorphisms.ModuleHomTransport

/-! # Restricted Hom Transport -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.RestrictedHomTransport

noncomputable section

/-! Transport of a morphism along open immersions is the actual
restriction of that morphism, through the canonical comparisons. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
variable [IsOpenImmersion f] [IsOpenImmersion g] {L M : Z.Modules}

theorem restriction_compare_transport
    (b : (Scheme.Modules.pullback g).obj L ⟶ (Scheme.Modules.pullback g).obj M) :
    (Scheme.Modules.restrictFunctorIsoPullback (f ≫ g)).hom.app L ≫
        ModuleHomTransport.Construction.moduleHomTransport g b f (f ≫ g) rfl ≫
          (Scheme.Modules.restrictFunctorIsoPullback (f ≫ g)).inv.app M =
      (Scheme.Modules.restrictFunctorComp f g).hom.app L ≫
        (Scheme.Modules.restrictFunctor f).map
          ((Scheme.Modules.restrictFunctorIsoPullback g).hom.app L ≫ b ≫
            (Scheme.Modules.restrictFunctorIsoPullback g).inv.app M) ≫
          (Scheme.Modules.restrictFunctorComp f g).inv.app M := by
  rw [ModuleHomTransport.Construction.moduleHomTransport_native g b f (f ≫ g) rfl]
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.trans_refl]
  apply (cancel_epi ((Scheme.Modules.restrictFunctorIsoPullback (f ≫ g)).inv.app L)).mp
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← OpenPullbackCoherence.Construction.restrictPullback_comp_inv f g M, ← OpenPullbackCoherence.Construction.restrictPullback_comp_inv f g L]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app_assoc]
  rw [← (Scheme.Modules.restrictFunctorIsoPullback f).inv.naturality_assoc
    ((Scheme.Modules.restrictFunctorIsoPullback g).hom.app L ≫ b ≫
      (Scheme.Modules.restrictFunctorIsoPullback g).inv.app M)]
  simp only [Functor.map_comp, Category.assoc]
  have hi := ((Scheme.Modules.pullback f).mapIso
    ((Scheme.Modules.restrictFunctorIsoPullback g).app L)).inv_hom_id
  change (Scheme.Modules.pullback f).map ((Scheme.Modules.restrictFunctorIsoPullback g).inv.app L) ≫
    (Scheme.Modules.pullback f).map ((Scheme.Modules.restrictFunctorIsoPullback g).hom.app L) = 𝟙 _ at hi
  rw [← Category.assoc ((Scheme.Modules.pullback f).map
    ((Scheme.Modules.restrictFunctorIsoPullback g).inv.app L)), hi, Category.id_comp]

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.RestrictedHomTransport
