import OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineRestrictionCoherence

/-! # Crystalline Sheaf Coherence -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineSheafCoherence

noncomputable section

/-!
# Coherence of the actual crystalline coefficient sheaves

The structure sheaf and constant sheaf identifications used by crystalline
pullback respect identity and composition of the underlying scheme maps.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Functor _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology
  CrystallineRestrictionCoherence SheafificationCoherence

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
variable {X Y Z : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)}
  {fY : Y ⟶ Spec (CommRingCat.of B)} {fZ : Z ⟶ Spec (CommRingCat.of B)}

theorem structureTransport_eq (g : X ⟶ Y) (hg : g ≫ fY = f) :
    IntegralComparison.BigCrystallineCohomology.structureTransport (p := p) (J := J) (δ := δ) g hg =
      SheafificationCoherence.transport IntegralComparison.BigCrystallineSite.Object.topology IntegralComparison.BigCrystallineSite.Object.topology (IntegralComparison.BigCrystallineSite.postcompose g hg) (IntegralComparison.BigCrystallineCohomology.largePresheaf fY) := by
  change SheafificationCoherence.transport IntegralComparison.BigCrystallineSite.Object.topology IntegralComparison.BigCrystallineSite.Object.topology (IntegralComparison.BigCrystallineSite.postcompose g hg) (IntegralComparison.BigCrystallineCohomology.largePresheaf fY) ≪≫
    (presheafToSheaf IntegralComparison.BigCrystallineSite.Object.topology (ModuleCat.{u + 1} (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)))).mapIso (Iso.refl _) = _
  rw [Functor.mapIso_refl, Iso.trans_refl]

theorem constantTransport_id : IntegralComparison.BigCrystallineCohomology.constantTransport (p := p) (J := J) (δ := δ)
    (𝟙 X) (Category.id_comp f) = CrystallineRestrictionCoherence.restrictionId.app (IntegralComparison.BigCrystallineCohomology.constantUnit f) := by
  have hn := ConstantRestrictionCoherence.transport_natIso IntegralComparison.BigCrystallineSite.Object.topology IntegralComparison.BigCrystallineSite.Object.topology
    (IntegralComparison.BigCrystallineSite.postcompose (p := p) (J := J) (δ := δ) (𝟙 X) (Category.id_comp f)) CrystallineRestrictionCoherence.postcomposeId
    (ModuleCat.of (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)) (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)))
  rw [ConstantRestrictionCoherence.transport_id] at hn
  exact hn

theorem restrictionId_app (P : IntegralComparison.Crystalline.ExactRestriction.ModuleSheaf (p := p) (J := J) (δ := δ) f) :
    CrystallineRestrictionCoherence.restrictionId.app P =
      (Functor.sheafPushforwardContinuousIso CrystallineRestrictionCoherence.postcomposeId
        (ModuleCat.{u + 1} (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B))) IntegralComparison.BigCrystallineSite.Object.topology IntegralComparison.BigCrystallineSite.Object.topology).app P := by
  apply Iso.ext
  ext U x
  rfl

theorem presheafTransport_id :
    IntegralComparison.BigCrystallineCohomology.presheafTransport (p := p) (J := J) (δ := δ) (𝟙 X) (Category.id_comp f) =
      (isoWhiskerRight (NatIso.op (CrystallineRestrictionCoherence.postcomposeId (p := p) (J := J) (δ := δ) (f := f)))
        (IntegralComparison.BigCrystallineCohomology.largePresheaf f)).symm := by
  apply Iso.ext
  ext U a
  rfl

theorem structureTransport_id : IntegralComparison.BigCrystallineCohomology.structureTransport (p := p) (J := J) (δ := δ)
    (𝟙 X) (Category.id_comp f) = CrystallineRestrictionCoherence.restrictionId.app (IntegralComparison.BigCrystallineCohomology.structureSheaf f) := by
  let F := IntegralComparison.BigCrystallineSite.postcompose (p := p) (J := J) (δ := δ) (𝟙 X) (Category.id_comp f)
  let Q := isoWhiskerRight (NatIso.op (CrystallineRestrictionCoherence.postcomposeId (p := p) (J := J) (δ := δ) (f := f)))
    (IntegralComparison.BigCrystallineCohomology.largePresheaf f)
  let S := presheafToSheaf (IntegralComparison.BigCrystallineSite.Object.topology (p := p) (J := J) (δ := δ) (f := f))
    (ModuleCat.{u + 1} (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)))
  have hm := congrArg (fun e : F.op ⋙ IntegralComparison.BigCrystallineCohomology.largePresheaf f ≅ IntegralComparison.BigCrystallineCohomology.largePresheaf f => S.mapIso e)
    (presheafTransport_id (p := p) (J := J) (δ := δ) (f := f))
  have hs : S.mapIso Q.symm = (S.mapIso Q).symm := rfl
  have ht := congrArg (fun e => SheafificationCoherence.transport IntegralComparison.BigCrystallineSite.Object.topology IntegralComparison.BigCrystallineSite.Object.topology F (IntegralComparison.BigCrystallineCohomology.largePresheaf f) ≪≫ e)
    (hm.trans hs)
  exact ht.trans ((SheafificationCoherence.transport_idIso IntegralComparison.BigCrystallineSite.Object.topology F CrystallineRestrictionCoherence.postcomposeId (IntegralComparison.BigCrystallineCohomology.largePresheaf f)).trans
    (restrictionId_app (IntegralComparison.BigCrystallineCohomology.structureSheaf f)).symm)

variable (g : X ⟶ Y) (hg : g ≫ fY = f) (h : Y ⟶ Z) (hh : h ≫ fZ = fY)

theorem constantTransport_comp :
    (IntegralComparison.Crystalline.ExactRestriction.restriction (p := p) (J := J) (δ := δ) g hg).mapIso (IntegralComparison.BigCrystallineCohomology.constantTransport h hh) ≪≫
      IntegralComparison.BigCrystallineCohomology.constantTransport g hg =
        (CrystallineRestrictionCoherence.restrictionComp g hg h hh).app (IntegralComparison.BigCrystallineCohomology.constantUnit fZ) ≪≫
          IntegralComparison.BigCrystallineCohomology.constantTransport (g ≫ h) (CrystallineRestrictionCoherence.composite_over g hg h hh) := by
  let := Functor.isContinuous_comp (IntegralComparison.BigCrystallineSite.postcompose (p := p) (J := J) (δ := δ) g hg)
    (IntegralComparison.BigCrystallineSite.postcompose h hh) IntegralComparison.BigCrystallineSite.Object.topology IntegralComparison.BigCrystallineSite.Object.topology IntegralComparison.BigCrystallineSite.Object.topology
  let := isCocontinuous_comp (IntegralComparison.BigCrystallineSite.postcompose (p := p) (J := J) (δ := δ) g hg)
    (IntegralComparison.BigCrystallineSite.postcompose h hh) IntegralComparison.BigCrystallineSite.Object.topology IntegralComparison.BigCrystallineSite.Object.topology (L := IntegralComparison.BigCrystallineSite.Object.topology)
  exact (ConstantRestrictionCoherence.transport_comp IntegralComparison.BigCrystallineSite.Object.topology IntegralComparison.BigCrystallineSite.Object.topology IntegralComparison.BigCrystallineSite.Object.topology
    (IntegralComparison.BigCrystallineSite.postcompose g hg) (IntegralComparison.BigCrystallineSite.postcompose h hh) (ModuleCat.of (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)) (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)))).trans
      (ConstantRestrictionCoherence.transport_natIso IntegralComparison.BigCrystallineSite.Object.topology IntegralComparison.BigCrystallineSite.Object.topology
        (IntegralComparison.BigCrystallineSite.postcompose g hg ⋙ IntegralComparison.BigCrystallineSite.postcompose h hh) (CrystallineRestrictionCoherence.postcomposeComp g hg h hh)
          (ModuleCat.of (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)) (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B))))

theorem structureTransport_comp :
    (IntegralComparison.Crystalline.ExactRestriction.restriction (p := p) (J := J) (δ := δ) g hg).mapIso (IntegralComparison.BigCrystallineCohomology.structureTransport h hh) ≪≫
      IntegralComparison.BigCrystallineCohomology.structureTransport g hg =
        (CrystallineRestrictionCoherence.restrictionComp g hg h hh).app (IntegralComparison.BigCrystallineCohomology.structureSheaf fZ) ≪≫
          IntegralComparison.BigCrystallineCohomology.structureTransport (g ≫ h) (CrystallineRestrictionCoherence.composite_over g hg h hh) := by
  let := Functor.isContinuous_comp (IntegralComparison.BigCrystallineSite.postcompose (p := p) (J := J) (δ := δ) g hg)
    (IntegralComparison.BigCrystallineSite.postcompose h hh) IntegralComparison.BigCrystallineSite.Object.topology IntegralComparison.BigCrystallineSite.Object.topology IntegralComparison.BigCrystallineSite.Object.topology
  let := isCocontinuous_comp (IntegralComparison.BigCrystallineSite.postcompose (p := p) (J := J) (δ := δ) g hg)
    (IntegralComparison.BigCrystallineSite.postcompose h hh) IntegralComparison.BigCrystallineSite.Object.topology IntegralComparison.BigCrystallineSite.Object.topology (L := IntegralComparison.BigCrystallineSite.Object.topology)
  have he : isoWhiskerRight (NatIso.op (CrystallineRestrictionCoherence.postcomposeComp (p := p) (J := J) (δ := δ) g hg h hh))
      (IntegralComparison.BigCrystallineCohomology.largePresheaf fZ) = Iso.refl _ := by
    apply Iso.ext
    ext U a
    rfl
  have hn := SheafificationCoherence.transport_natIso IntegralComparison.BigCrystallineSite.Object.topology IntegralComparison.BigCrystallineSite.Object.topology
    (IntegralComparison.BigCrystallineSite.postcompose (p := p) (J := J) (δ := δ) g hg ⋙ IntegralComparison.BigCrystallineSite.postcompose h hh)
    (CrystallineRestrictionCoherence.postcomposeComp g hg h hh) (IntegralComparison.BigCrystallineCohomology.largePresheaf fZ)
  have hm : (presheafToSheaf IntegralComparison.BigCrystallineSite.Object.topology (ModuleCat.{u + 1} (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)))).mapIso
      (isoWhiskerRight (NatIso.op (CrystallineRestrictionCoherence.postcomposeComp (p := p) (J := J) (δ := δ) g hg h hh))
        (IntegralComparison.BigCrystallineCohomology.largePresheaf fZ)) = Iso.refl (IntegralComparison.BigCrystallineCohomology.structureSheaf f) :=
    (congrArg (fun e : IntegralComparison.BigCrystallineCohomology.largePresheaf f ≅ IntegralComparison.BigCrystallineCohomology.largePresheaf f =>
      (presheafToSheaf IntegralComparison.BigCrystallineSite.Object.topology (ModuleCat.{u + 1} (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)))).mapIso e) he).trans
      (Functor.mapIso_refl _ _)
  let c := (CrystallineRestrictionCoherence.restrictionComp (p := p) (J := J) (δ := δ) g hg h hh).app (IntegralComparison.BigCrystallineCohomology.structureSheaf fZ)
  let t := SheafificationCoherence.transport IntegralComparison.BigCrystallineSite.Object.topology IntegralComparison.BigCrystallineSite.Object.topology
    (IntegralComparison.BigCrystallineSite.postcompose (p := p) (J := J) (δ := δ) (g ≫ h) (CrystallineRestrictionCoherence.composite_over g hg h hh)) (IntegralComparison.BigCrystallineCohomology.largePresheaf fZ)
  have hs := (congrArg (fun e : IntegralComparison.BigCrystallineCohomology.structureSheaf f ≅ IntegralComparison.BigCrystallineCohomology.structureSheaf f => c ≪≫ t ≪≫ e) hm).trans
    (congrArg (fun e => c ≪≫ e) (Iso.trans_refl t))
  have hl := congrArg₂ (fun a b => (IntegralComparison.Crystalline.ExactRestriction.restriction (p := p) (J := J) (δ := δ) g hg).mapIso a ≪≫ b)
    (structureTransport_eq (p := p) (J := J) (δ := δ) h hh)
    (structureTransport_eq (p := p) (J := J) (δ := δ) g hg)
  have hr := congrArg (fun e => c ≪≫ e)
    (structureTransport_eq (p := p) (J := J) (δ := δ) (g ≫ h) (CrystallineRestrictionCoherence.composite_over g hg h hh))
  exact hl.trans ((SheafificationCoherence.transport_comp IntegralComparison.BigCrystallineSite.Object.topology IntegralComparison.BigCrystallineSite.Object.topology IntegralComparison.BigCrystallineSite.Object.topology
    (IntegralComparison.BigCrystallineSite.postcompose g hg) (IntegralComparison.BigCrystallineSite.postcompose h hh) (IntegralComparison.BigCrystallineCohomology.largePresheaf fZ)).trans
      ((hn.trans hs).trans hr.symm))

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineSheafCoherence
