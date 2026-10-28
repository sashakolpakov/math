import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnitPullbackCoherence

/-! # Open Pullback Coherence -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.OpenPullbackCoherence

noncomputable section

/-! The native restriction-to-pullback comparison respects composition
of open immersions, with its actual adjunction normalization retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {X Y Z : Scheme.{u}}

theorem pullback_restrict_inv_homEquiv (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
      ((Scheme.Modules.restrictFunctorIsoPullback f).inv.app M) =
        (Scheme.Modules.restrictAdjunction f).unit.app M := by
  rw [Scheme.Modules.restrictFunctorIsoPullback, Adjunction.leftAdjointUniq_inv_app,
    Adjunction.homEquiv_leftAdjointUniq_hom_app]

theorem restrictAdjunction_unit_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] (M : Z.Modules) :
    ((Scheme.Modules.restrictAdjunction g).unit.app M ≫
      (Scheme.Modules.pushforward g).map
        ((Scheme.Modules.restrictAdjunction f).unit.app (M.restrict g) ≫
          (Scheme.Modules.pushforward f).map ((Scheme.Modules.restrictFunctorComp f g).inv.app M))) ≫
      (Scheme.Modules.pushforwardComp f g).hom.app (M.restrict (f ≫ g)) =
        (Scheme.Modules.restrictAdjunction (f ≫ g)).unit.app M := by
  apply Scheme.Modules.hom_ext
  intro U
  ext m
  let V := f ⁻¹ᵁ (g ⁻¹ᵁ U)
  let a := homOfLE (g.image_preimage_le U)
  let b := g.opensFunctor.map (homOfLE (f.image_preimage_le (g ⁻¹ᵁ U)))
  let c : (f ≫ g) ''ᵁ V ⟶ g ''ᵁ (f ''ᵁ V) := eqToHom (by simp)
  let d : (f ≫ g) ''ᵁ V ⟶ U := homOfLE ((f ≫ g).image_preimage_le U)
  change M.presheaf.map c.op (M.presheaf.map b.op (M.presheaf.map a.op m)) = M.presheaf.map d.op m
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
  exact congrArg (fun i => M.presheaf.map i m) (Subsingleton.elim _ _)

theorem restrictPullback_comp_inv (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] (M : Z.Modules) :
    (Scheme.Modules.pullbackComp f g).inv.app M ≫
      (Scheme.Modules.pullback f).map ((Scheme.Modules.restrictFunctorIsoPullback g).inv.app M) ≫
        (Scheme.Modules.restrictFunctorIsoPullback f).inv.app (M.restrict g) ≫
          (Scheme.Modules.restrictFunctorComp f g).inv.app M =
      (Scheme.Modules.restrictFunctorIsoPullback (f ≫ g)).inv.app M := by
  let ag := Scheme.Modules.pullbackPushforwardAdjunction g
  let af := Scheme.Modules.pullbackPushforwardAdjunction f
  let ac := Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)
  have hf : af.homEquiv _ _ ((Scheme.Modules.restrictFunctorIsoPullback f).inv.app (M.restrict g)) =
      (Scheme.Modules.restrictAdjunction f).unit.app (M.restrict g) :=
    pullback_restrict_inv_homEquiv f (M.restrict g)
  have hg : ag.homEquiv _ _ ((Scheme.Modules.restrictFunctorIsoPullback g).inv.app M) =
      (Scheme.Modules.restrictAdjunction g).unit.app M := pullback_restrict_inv_homEquiv g M
  have hc : ac.homEquiv _ _ ((Scheme.Modules.restrictFunctorIsoPullback (f ≫ g)).inv.app M) =
      (Scheme.Modules.restrictAdjunction (f ≫ g)).unit.app M :=
    pullback_restrict_inv_homEquiv (f ≫ g) M
  apply (ac.homEquiv _ _).injective
  rw [UnitPullbackCoherence.Construction.homEquiv_conjugate (ag.comp af) ac,
    Scheme.Modules.conjugateEquiv_pullbackComp_inv]
  change ag.homEquiv _ _ (af.homEquiv _ _
      ((Scheme.Modules.pullback f).map ((Scheme.Modules.restrictFunctorIsoPullback g).inv.app M) ≫
        (Scheme.Modules.restrictFunctorIsoPullback f).inv.app (M.restrict g) ≫
          (Scheme.Modules.restrictFunctorComp f g).inv.app M)) ≫
      (Scheme.Modules.pushforwardComp f g).hom.app (M.restrict (f ≫ g)) = _
  rw [af.homEquiv_naturality_left, af.homEquiv_naturality_right, hf,
    ag.homEquiv_naturality_right, hg, hc]
  exact restrictAdjunction_unit_comp f g M

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.OpenPullbackCoherence
