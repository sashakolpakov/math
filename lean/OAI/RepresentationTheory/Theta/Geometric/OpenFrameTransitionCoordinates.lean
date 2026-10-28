import OAI.RepresentationTheory.Theta.Geometric.OpenTopUnitGluing
import OAI.RepresentationTheory.Theta.Geometric.ModuleIsoFrameUnits
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.IsoUnitPullback
import OAI.RepresentationTheory.Theta.Geometric.Pullback.OpenFrameRestriction

/-! # Open Frame Transition Coordinates -/

namespace OAI.RepresentationTheory.Theta.Geometric.OpenFrameTransitionCoordinates

noncomputable section

section

/-! Overlap coefficients of native frames, and the compatibility
equations satisfied by an actual line-bundle isomorphism. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

def openFrameTransitionTopUnit {X : Scheme} (M : X.Modules) (U V : X.Opens)
    (e : M.restrict U.ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.toScheme)
    (g : M.restrict V.ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj V.toScheme) : Γ((U ⊓ V).toScheme, ⊤)ˣ :=
  IntrinsicFrame.TransitionUnits.frameTransitionTopUnit (AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization inf_le_left e)
    (AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization inf_le_right g)

theorem openFrameTransitionTopUnit_spec {X : Scheme} (M : X.Modules) (U V : X.Opens)
    (e : M.restrict U.ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.toScheme)
    (g : M.restrict V.ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj V.toScheme) :
    (AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (show U ⊓ V ≤ U from inf_le_left) e).hom =
      (AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (show U ⊓ V ≤ V from inf_le_right) g).hom ≫
        AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection (openFrameTransitionTopUnit M U V e g : Γ((U ⊓ V).toScheme, ⊤)) :=
  IntrinsicFrame.TransitionUnits.frameTransitionTopUnit_spec _ _

def moduleIsoOpenTopUnit {X : Scheme} {M N : X.Modules} (a : M ≅ N) (U : X.Opens)
    (e : M.restrict U.ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.toScheme)
    (g : N.restrict U.ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.toScheme) : Γ(U.toScheme, ⊤)ˣ :=
  Units.map U.topIso.inv.hom.toMonoidHom (ModuleIsoFrameUnits.moduleIsoFrameUnit a U e g)

theorem moduleIsoOpenTopUnit_transition {X : Scheme} {M N : X.Modules} (a : M ≅ N)
    (U V : X.Opens)
    (eU : M.restrict U.ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.toScheme)
    (eV : M.restrict V.ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj V.toScheme)
    (gU : N.restrict U.ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.toScheme)
    (gV : N.restrict V.ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj V.toScheme) :
    (openFrameTransitionTopUnit M U V eU eV : Γ((U ⊓ V).toScheme, ⊤)) *
        (X.homOfLE (show U ⊓ V ≤ U from inf_le_left)).appTop (moduleIsoOpenTopUnit a U eU gU) =
      (X.homOfLE (show U ⊓ V ≤ V from inf_le_right)).appTop (moduleIsoOpenTopUnit a V eV gV) *
        (openFrameTransitionTopUnit N U V gU gV : Γ((U ⊓ V).toScheme, ⊤)) := by
  have H := ModuleIsoFrameUnits.moduleIsoFrameUnit_transition a (U ⊓ V)
    (AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization inf_le_left eU)
    (AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization inf_le_right eV)
    (AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization inf_le_left gU)
    (AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization inf_le_right gV)
  rw [← ModuleIsoFrameUnits.moduleIsoFrameUnit_restrict, ← ModuleIsoFrameUnits.moduleIsoFrameUnit_restrict] at H
  have HH := congrArg (fun u : Γ(X, U ⊓ V)ˣ => (U ⊓ V).topIso.inv (u : Γ(X, U ⊓ V))) H
  change (U ⊓ V).topIso.inv
      ((X.presheaf.map (homOfLE (show U ⊓ V ≤ U from inf_le_left)).op (ModuleIsoFrameUnits.moduleIsoFrameUnit a U eU gU)) *
        (U ⊓ V).topIso.hom (openFrameTransitionTopUnit M U V eU eV)) =
    (U ⊓ V).topIso.inv
      ((U ⊓ V).topIso.hom (openFrameTransitionTopUnit N U V gU gV) *
        X.presheaf.map (homOfLE (show U ⊓ V ≤ V from inf_le_right)).op (ModuleIsoFrameUnits.moduleIsoFrameUnit a V eV gV)) at HH
  rw [map_mul, map_mul, OpenTopUnitGluing.openTopSection_restrict, OpenTopUnitGluing.openTopSection_restrict,
    Iso.hom_inv_id_apply, Iso.hom_inv_id_apply] at HH
  exact (mul_comm _ _).trans (HH.trans (mul_comm _ _))

theorem openFrameTransitionTopUnit_pullback {X Y : Scheme} (f : X ⟶ Y) (M : Y.Modules)
    (U V : Y.Opens)
    (e : M.restrict U.ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.toScheme)
    (g : M.restrict V.ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj V.toScheme) :
    openFrameTransitionTopUnit ((Scheme.Modules.pullback f).obj M) (f ⁻¹ᵁ U) (f ⁻¹ᵁ V)
        (Pullback.Algebraic.pullbackOpenFrame f M U e) (Pullback.Algebraic.pullbackOpenFrame f M V g) =
      Units.map (f ∣_ (U ⊓ V)).appTop.hom.toMonoidHom (openFrameTransitionTopUnit M U V e g) := by
  symm
  apply Intrinsic.IsoUnitPullback.frameTransitionTopUnit_unique
  have hl := congrArg Iso.hom (Pullback.OpenFrameRestriction.pullbackOpenFrame_restrict f M (show U ⊓ V ≤ U from inf_le_left) e)
  have hr := congrArg Iso.hom (Pullback.OpenFrameRestriction.pullbackOpenFrame_restrict f M (show U ⊓ V ≤ V from inf_le_right) g)
  exact hl.trans ((Pullback.Algebraic.pullbackOpenFrame_scalar f M (U ⊓ V) _ _ _
    (openFrameTransitionTopUnit_spec M U V e g)).trans
      (congrArg (fun t => t ≫ AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection
        ((f ∣_ (U ⊓ V)).appTop (openFrameTransitionTopUnit M U V e g))) hr.symm))

end

/-! Actual isomorphism coefficients satisfy the pulled-back transition
equations in the global section rings of the native overlap schemes. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem pullbackOpenFrame_transition_scalar {X Y : Scheme} (f : X ⟶ Y) (M : Y.Modules)
    (U V : Y.Opens)
    (e : M.restrict U.ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.toScheme)
    (g : M.restrict V.ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj V.toScheme) :
    (AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (show f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U from inf_le_left)
      (Pullback.Algebraic.pullbackOpenFrame f M U e)).hom =
    (AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (show f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V ≤ f ⁻¹ᵁ V from inf_le_right)
      (Pullback.Algebraic.pullbackOpenFrame f M V g)).hom ≫ AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection
        ((f ∣_ (U ⊓ V)).appTop (openFrameTransitionTopUnit M U V e g)) := by
  have hl := congrArg Iso.hom (Pullback.OpenFrameRestriction.pullbackOpenFrame_restrict f M (show U ⊓ V ≤ U from inf_le_left) e)
  have hr := congrArg Iso.hom (Pullback.OpenFrameRestriction.pullbackOpenFrame_restrict f M (show U ⊓ V ≤ V from inf_le_right) g)
  exact hl.trans ((Pullback.Algebraic.pullbackOpenFrame_scalar f M (U ⊓ V) _ _ _
    (openFrameTransitionTopUnit_spec M U V e g)).trans
      (congrArg (fun t => t ≫ AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection
        ((f ∣_ (U ⊓ V)).appTop (openFrameTransitionTopUnit M U V e g))) hr.symm))

theorem moduleIsoOpenTopUnit_pullback_transition {X Y : Scheme} (f : X ⟶ Y) {M N : Y.Modules}
    (a : (Scheme.Modules.pullback f).obj M ≅ (Scheme.Modules.pullback f).obj N)
    (U V : Y.Opens)
    (eU : M.restrict U.ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.toScheme)
    (eV : M.restrict V.ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj V.toScheme)
    (gU : N.restrict U.ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.toScheme)
    (gV : N.restrict V.ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj V.toScheme) :
    (f ∣_ (U ⊓ V)).appTop (openFrameTransitionTopUnit M U V eU eV) *
      (X.homOfLE (f.preimage_mono (show U ⊓ V ≤ U from inf_le_left))).appTop
        (moduleIsoOpenTopUnit a (f ⁻¹ᵁ U) (Pullback.Algebraic.pullbackOpenFrame f M U eU) (Pullback.Algebraic.pullbackOpenFrame f N U gU)) =
    (X.homOfLE (f.preimage_mono (show U ⊓ V ≤ V from inf_le_right))).appTop
        (moduleIsoOpenTopUnit a (f ⁻¹ᵁ V) (Pullback.Algebraic.pullbackOpenFrame f M V eV) (Pullback.Algebraic.pullbackOpenFrame f N V gV)) *
      (f ∣_ (U ⊓ V)).appTop (openFrameTransitionTopUnit N U V gU gV) := by
  have H := moduleIsoOpenTopUnit_transition a (f ⁻¹ᵁ U) (f ⁻¹ᵁ V)
    (Pullback.Algebraic.pullbackOpenFrame f M U eU) (Pullback.Algebraic.pullbackOpenFrame f M V eV)
    (Pullback.Algebraic.pullbackOpenFrame f N U gU) (Pullback.Algebraic.pullbackOpenFrame f N V gV)
  have hM := congrArg Units.val (openFrameTransitionTopUnit_pullback f M U V eU eV)
  have hN := congrArg Units.val (openFrameTransitionTopUnit_pullback f N U V gU gV)
  exact (congrArg (fun t => t *
    (X.homOfLE (f.preimage_mono (show U ⊓ V ≤ U from inf_le_left))).appTop
      (moduleIsoOpenTopUnit a (f ⁻¹ᵁ U) (Pullback.Algebraic.pullbackOpenFrame f M U eU) (Pullback.Algebraic.pullbackOpenFrame f N U gU))) hM).symm.trans
      (H.trans (congrArg (fun t =>
        (X.homOfLE (f.preimage_mono (show U ⊓ V ≤ V from inf_le_right))).appTop
          (moduleIsoOpenTopUnit a (f ⁻¹ᵁ V) (Pullback.Algebraic.pullbackOpenFrame f M V eV) (Pullback.Algebraic.pullbackOpenFrame f N V gV)) * t) hN))

end

end OAI.RepresentationTheory.Theta.Geometric.OpenFrameTransitionCoordinates
