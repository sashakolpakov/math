import OAI.AlgebraicGeometry.Quotients.FiniteDescent.OpenPullbackIs

/-! # Open Adjunction -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.OpenAdjunction.Construction

noncomputable section

/-! Restriction of the actual pullback/direct-image adjunction to an open subset. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

universe u

/-- Adjunction on an open is compatible with the canonical open base-change map. -/
theorem openRestriction_homEquiv {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    {M : Y.Modules} {N : X.Modules} (a : (Scheme.Modules.pullback f).obj M ⟶ N) :
    ((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).homEquiv _ _)
      ((Quotients.FiniteDescent.OpenPullbackIs.Construction.OpenPullbackSquare.adjointPullbackSquare f U).hom.app M ≫
        (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map a) =
      (Scheme.Modules.restrictFunctor U.ι).map
        (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _) a) ≫
          (Quotients.FiniteDescent.OpenPullbackIs.Construction.OpenPullbackSquare.openBaseChangeMap f U).app N := by
  change _ ≫ (Scheme.Modules.pushforward (f ∣_ U)).map (_ ≫ _) = _
  rw [Functor.map_comp, ← Category.assoc,
    ← Quotients.FiniteDescent.OpenPullbackIs.Construction.OpenPullbackSquare.unit_square]
  have hn := (Quotients.FiniteDescent.OpenPullbackIs.Construction.OpenPullbackSquare.openBaseChangeMap f U).naturality a
  dsimp only [Functor.comp_map] at hn
  rw [Category.assoc, ← hn, ← Category.assoc, ← Functor.map_comp]
  rfl

theorem openBaseChange_apply {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (M : X.Modules) (V : U.toScheme.Opens) (s : Γ(M, f ⁻¹ᵁ (U.ι ''ᵁ V))) :
    @Eq Γ(M, (f ⁻¹ᵁ U).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V))
      (((Quotients.FiniteDescent.OpenPullbackIs.Construction.OpenPullbackSquare.openBaseChangeMap f U).app M).app V s)
      (M.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V)).op s) :=
  ConcreteCategory.congr_hom (Quotients.FiniteDescent.OpenPullbackIs.Construction.OpenPullbackSquare.map_app f U M V) s

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.OpenAdjunction.Construction
