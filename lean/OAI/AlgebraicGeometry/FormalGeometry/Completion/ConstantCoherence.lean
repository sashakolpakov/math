import OAI.AlgebraicGeometry.FormalGeometry.Completion.PullbackCoherence

/-! # Constant Coherence -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.ConstantCoherence.Construction

/-! # Completion: coherence of inverse image on constant sheaves -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

section ConstantSheaf

variable {C D : Type*} [Category* C] [Category* D]
    (J : GrothendieckTopology C) [HasWeakSheafify J D]

/-- The unit for a constant sheaf is the sheafification unit at the terminal object. -/
theorem constantSheafAdj_unit_at {T : C} (hT : IsTerminal T) (P : D) :
    (constantSheafAdj J D hT).unit.app P =
      (toSheafify J ((Functor.const Cᵒᵖ).obj P)).app (op T) := by
  simp [constantSheafAdj, Adjunction.comp_unit_app, constantPresheafAdj]

/-- Constant-sheaf units at terminal objects agree under restriction. -/
theorem constantSheafAdj_unit_restrict {T U : C} (hT : IsTerminal T) (hU : IsTerminal U)
    (f : T ⟶ U) (P : D) :
    (constantSheafAdj J D hU).unit.app P ≫
        ((constantSheaf J D).obj P).obj.map f.op =
      (constantSheafAdj J D hT).unit.app P := by
  rw [constantSheafAdj_unit_at, constantSheafAdj_unit_at]
  simpa using! ((toSheafify J ((Functor.const Cᵒᵖ).obj P)).naturality f.op).symm

end ConstantSheaf

/-- The canonical map from a constant sheaf into the direct image of a constant sheaf. -/
noncomputable def proEtConstantToPushforward {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : Ab.{u + 1}) :
    (constantSheaf (Scheme.ProEt.topology Y) Ab.{u + 1}).obj P ⟶
      ((ProetalePullback.Construction.proEtBaseChange f).sheafPushforwardContinuous Ab.{u + 1}
        (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).obj
          ((constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).obj P) :=
  ((sheafificationAdjunction (Scheme.ProEt.topology Y) Ab.{u + 1}).homEquiv _ _).symm
    (Functor.whiskerLeft (ProetalePullback.Construction.proEtBaseChange f).op
      (toSheafify (Scheme.ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj P)))

/-- The defining universal property of the constant direct-image map. -/
theorem proEtConstantToPushforward_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : Ab.{u + 1}) :
    toSheafify (Scheme.ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj P) ≫
        (proEtConstantToPushforward f P).hom =
      Functor.whiskerLeft (ProetalePullback.Construction.proEtBaseChange f).op
        (toSheafify (Scheme.ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj P)) := by
  exact ((sheafificationAdjunction (Scheme.ProEt.topology Y) Ab.{u + 1}).homEquiv _ _).apply_symm_apply _

@[reassoc]
theorem proEtConstantToPushforward_unit_app {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : Ab.{u + 1}) (U : Y.ProEtᵒᵖ) :
    (toSheafify (Scheme.ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj P)).app U ≫
        (proEtConstantToPushforward f P).hom.app U =
      (toSheafify (Scheme.ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj P)).app
        ((ProetalePullback.Construction.proEtBaseChange f).op.obj U) :=
  congr_app (proEtConstantToPushforward_unit f P) U

/-- Canonical maps of constant sheaves commute with composition. -/
theorem proEtConstantToPushforward_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : Ab.{u + 1}) :
    proEtConstantToPushforward (f ≫ g) P =
      proEtConstantToPushforward g P ≫
        ((ProetalePullback.Construction.proEtBaseChange g).sheafPushforwardContinuous Ab.{u + 1}
          (Scheme.ProEt.topology Z) (Scheme.ProEt.topology Y)).map
            (proEtConstantToPushforward f P) ≫
        (PullbackCoherence.Construction.proEtSheafPushforwardCompIso f g).hom.app
          ((constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).obj P) := by
  apply ((sheafificationAdjunction (Scheme.ProEt.topology Z) Ab.{u + 1}).homEquiv _ _).injective
  change toSheafify (Scheme.ProEt.topology Z) ((Functor.const Z.ProEtᵒᵖ).obj P) ≫ _ =
    toSheafify (Scheme.ProEt.topology Z) ((Functor.const Z.ProEtᵒᵖ).obj P) ≫ _
  apply NatTrans.ext
  funext U
  change (toSheafify (Scheme.ProEt.topology Z) ((Functor.const Z.ProEtᵒᵖ).obj P)).app U ≫
      (proEtConstantToPushforward (f ≫ g) P).hom.app U =
    (toSheafify (Scheme.ProEt.topology Z) ((Functor.const Z.ProEtᵒᵖ).obj P)).app U ≫
      (proEtConstantToPushforward g P).hom.app U ≫
      (proEtConstantToPushforward f P).hom.app ((ProetalePullback.Construction.proEtBaseChange g).op.obj U) ≫
      ((constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).obj P).obj.map
        (((PullbackCoherence.Construction.proEtBaseChangeCompIso f g).hom.app U.unop).op)
  erw [proEtConstantToPushforward_unit_app, proEtConstantToPushforward_unit_app_assoc,
    proEtConstantToPushforward_unit_app_assoc]
  simpa using! (toSheafify (Scheme.ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).obj P)).naturality
      (((PullbackCoherence.Construction.proEtBaseChangeCompIso f g).hom.app U.unop).op)

/-- The inverse-image constant comparison is adjoint to the canonical map. -/
theorem proEtConstantPullbackIso_adjoint {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : Ab.{u + 1}) :
    ((ProetalePullback.Construction.proEtBaseChange f).sheafAdjunctionContinuous Ab.{u + 1}
      (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).homEquiv _ _
        ((ProetalePullback.Construction.proEtConstantPullbackIso f).hom.app P) = proEtConstantToPushforward f P := by
  let c := constantSheafAdj (Scheme.ProEt.topology Y) Ab.{u + 1}
    (terminalIsTerminal (C := Y.ProEt))
  let a := (ProetalePullback.Construction.proEtBaseChange f).sheafAdjunctionContinuous Ab.{u + 1}
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
  apply (c.homEquiv _ _).injective
  change (c.comp a).homEquiv _ _ ((ProetalePullback.Construction.proEtConstantPullbackIso f).hom.app P) = _
  rw [ProetalePullback.Construction.proEtConstantPullbackIso, Adjunction.homEquiv_leftAdjointUniq_hom_app,
    constantSheafAdj_unit_at]
  change _ = (constantPresheafAdj Ab.{u + 1}
    (terminalIsTerminal (C := Y.ProEt))).homEquiv _ _
      ((sheafificationAdjunction (Scheme.ProEt.topology Y) Ab.{u + 1}).homEquiv _ _
        (proEtConstantToPushforward f P))
  change _ = (constantPresheafAdj Ab.{u + 1}
    (terminalIsTerminal (C := Y.ProEt))).homEquiv _ _
      (toSheafify (Scheme.ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj P) ≫
        (proEtConstantToPushforward f P).hom)
  rw [proEtConstantToPushforward_unit, Adjunction.homEquiv_unit]
  simp [constantPresheafAdj]

/-- The constant-sheaf comparison for identity inverse image is canonical. -/
theorem proEtConstantPullbackIso_id (X : Scheme.{u}) (P : Ab.{u + 1}) :
    (ProetalePullback.Construction.proEtConstantPullbackIso (𝟙 X)).hom.app P =
      (PullbackCoherence.Construction.proEtSheafPullbackIdIso X).hom.app ((constantSheaf (Scheme.ProEt.topology X)
        Ab.{u + 1}).obj P) := by
  let a := (ProetalePullback.Construction.proEtBaseChange (𝟙 X)).sheafAdjunctionContinuous Ab.{u + 1}
    (Scheme.ProEt.topology X) (Scheme.ProEt.topology X)
  let c := constantSheafAdj (Scheme.ProEt.topology X) Ab.{u + 1}
    (terminalIsTerminal (C := X.ProEt))
  apply ((c.comp a).homEquiv _ _).injective
  change (c.comp a).homEquiv _ _
    (((c.comp a).leftAdjointUniq (constantSheafAdj (Scheme.ProEt.topology X) Ab.{u + 1}
      (terminalIsTerminal.isTerminalObj (ProetalePullback.Construction.proEtBaseChange (𝟙 X)) (⊤_ X.ProEt)))).hom.app P) = _
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app, Adjunction.comp_homEquiv]
  change _ = c.homEquiv P _ (a.homEquiv _ _
    ((a.leftAdjointIdIso (PullbackCoherence.Construction.proEtSheafPushforwardIdIso X)).hom.app _))
  erw [← AdjunctionCoherence.Construction.adjunction_id_adjoint a (PullbackCoherence.Construction.proEtSheafPushforwardIdIso X), Equiv.apply_symm_apply,
    Adjunction.homEquiv_unit]
  exact (constantSheafAdj_unit_restrict (Scheme.ProEt.topology X)
    (terminalIsTerminal.isTerminalObj (ProetalePullback.Construction.proEtBaseChange (𝟙 X)) (⊤_ X.ProEt))
    terminalIsTerminal ((PullbackCoherence.Construction.proEtBaseChangeIdIso X).hom.app (⊤_ X.ProEt)) P).symm

/-- Constant-sheaf inverse-image comparisons commute with composition. -/
theorem proEtConstantPullbackIso_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : Ab.{u + 1}) :
    (PullbackCoherence.Construction.proEtSheafPullbackCompIso f g).hom.app
        ((constantSheaf (Scheme.ProEt.topology Z) Ab.{u + 1}).obj P) ≫
      (ProetalePullback.Construction.proEtConstantPullbackIso (f ≫ g)).hom.app P =
        (ProetalePullback.Construction.proEtSheafPullback f).map ((ProetalePullback.Construction.proEtConstantPullbackIso g).hom.app P) ≫
          (ProetalePullback.Construction.proEtConstantPullbackIso f).hom.app P := by
  have h := AdjunctionCoherence.Construction.adjunction_comp_adjoint
    ((ProetalePullback.Construction.proEtBaseChange g).sheafAdjunctionContinuous Ab.{u + 1} _ _)
    ((ProetalePullback.Construction.proEtBaseChange f).sheafAdjunctionContinuous Ab.{u + 1} _ _)
    ((ProetalePullback.Construction.proEtBaseChange (f ≫ g)).sheafAdjunctionContinuous Ab.{u + 1} _ _)
    (PullbackCoherence.Construction.proEtSheafPushforwardCompIso f g)
    (proEtConstantToPushforward g P) (proEtConstantToPushforward f P)
  rw [← proEtConstantToPushforward_comp] at h
  rw [← proEtConstantPullbackIso_adjoint (f ≫ g) P,
    ← proEtConstantPullbackIso_adjoint g P,
    ← proEtConstantPullbackIso_adjoint f P] at h
  simpa only [Equiv.symm_apply_apply] using! h

/-- The inverse constant comparisons have the order used by cohomological pullback. -/
theorem proEtConstantPullbackIso_inv_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : Ab.{u + 1}) :
    (ProetalePullback.Construction.proEtConstantPullbackIso f).inv.app P ≫
        (ProetalePullback.Construction.proEtSheafPullback f).map ((ProetalePullback.Construction.proEtConstantPullbackIso g).inv.app P) =
      (ProetalePullback.Construction.proEtConstantPullbackIso (f ≫ g)).inv.app P ≫
        (PullbackCoherence.Construction.proEtSheafPullbackCompIso f g).inv.app
          ((constantSheaf (Scheme.ProEt.topology Z) Ab.{u + 1}).obj P) := by
  rw [← cancel_mono ((PullbackCoherence.Construction.proEtSheafPullbackCompIso f g).hom.app
    ((constantSheaf (Scheme.ProEt.topology Z) Ab.{u + 1}).obj P))]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [← cancel_mono ((ProetalePullback.Construction.proEtConstantPullbackIso (f ≫ g)).hom.app P),
    Category.assoc, Category.assoc, proEtConstantPullbackIso_comp]
  simp [← Functor.map_comp_assoc]

end OAI.AlgebraicGeometry.FormalGeometry.Completion.ConstantCoherence.Construction
