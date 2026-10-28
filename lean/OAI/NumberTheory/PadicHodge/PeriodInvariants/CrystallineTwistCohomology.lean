import OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistRestriction
import OAI.NumberTheory.PadicHodge.PeriodInvariants.SheafCoefficients
import OAI.NumberTheory.PadicHodge.PeriodInvariants.SemilinearExt
import OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology

/-! # Crystalline Twist Cohomology -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology

noncomputable section

/-!
# Semilinear base change on actual crystalline cohomology

Restriction along the base twist, followed by the inverse change of
coefficient modules, identifies the actual structure and constant
sheaves. The resulting Ext map is semilinear over the base automorphism.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology
open OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineBaseTwist OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistRestriction OAI.NumberTheory.PadicHodge.PeriodInvariants.SheafCoefficients

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
variable {X : Scheme.{u}} {f f' : X ⟶ Spec (CommRingCat.of B)}
variable (e : B ≃+* B) (he : DividedPowers.IsDPMorphism δ δ e.toRingHom)
  (he' : DividedPowers.IsDPMorphism δ δ e.symm.toRingHom)
  (h : f' = f ≫ Spec.map (CommRingCat.ofHom e.toRingHom))

def coefficientEquiv : IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B) ≃+* IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B) :=
  (ULift.ringEquiv.trans e).trans ULift.ringEquiv.symm

def twistedRestriction : IntegralComparison.Crystalline.ExactRestriction.ModuleSheaf (p := p) (J := J) (δ := δ) f' ⥤
    IntegralComparison.Crystalline.ExactRestriction.ModuleSheaf (p := p) (J := J) (δ := δ) f :=
  CrystallineTwistRestriction.restriction e he he' h ⋙
    SheafCoefficients.changeCoefficients IntegralComparison.BigCrystallineSite.Object.topology (coefficientEquiv e).symm

instance twistedRestriction_additive : (twistedRestriction (p := p) e he he' h).Additive := by
  dsimp only [twistedRestriction]
  infer_instance

instance twistedRestriction_preservesFiniteLimits :
    PreservesFiniteLimits (twistedRestriction (p := p) e he he' h) := by
  dsimp only [twistedRestriction]
  infer_instance

instance twistedRestriction_preservesFiniteColimits :
    PreservesFiniteColimits (twistedRestriction (p := p) e he he' h) := by
  dsimp only [twistedRestriction]
  infer_instance

def presheafTransport :
    ((CrystallineBaseTwist.twist (p := p) e he h).op ⋙ IntegralComparison.BigCrystallineCohomology.largePresheaf f') ⋙
        ModuleCat.restrictScalars (coefficientEquiv e).symm.toRingHom ≅ IntegralComparison.BigCrystallineCohomology.largePresheaf f :=
  NatIso.ofComponents (fun U =>
    { hom := ModuleCat.ofHom
        (X := (ModuleCat.restrictScalars (coefficientEquiv e).symm.toRingHom).obj
          (((CrystallineBaseTwist.twist (p := p) e he h).op ⋙ IntegralComparison.BigCrystallineCohomology.largePresheaf f').obj U))
        (Y := (IntegralComparison.BigCrystallineCohomology.largePresheaf f).obj U)
        { toFun := fun x => x
          map_add' := fun _ _ => rfl
          map_smul' := fun b x => by
            change (⟨U.unop.base (e (e.symm b.down)) * (show U.unop.ring from x.down)⟩ : ULift U.unop.ring) =
              ⟨U.unop.base b.down * (show U.unop.ring from x.down)⟩
            rw [e.apply_symm_apply] }
      inv := ModuleCat.ofHom
        (X := (IntegralComparison.BigCrystallineCohomology.largePresheaf f).obj U)
        (Y := (ModuleCat.restrictScalars (coefficientEquiv e).symm.toRingHom).obj
          (((CrystallineBaseTwist.twist (p := p) e he h).op ⋙ IntegralComparison.BigCrystallineCohomology.largePresheaf f').obj U))
        { toFun := fun x => x
          map_add' := fun _ _ => rfl
          map_smul' := fun b x => by
            change (⟨U.unop.base b.down * (show U.unop.ring from x.down)⟩ : ULift U.unop.ring) =
              ⟨U.unop.base (e (e.symm b.down)) * (show U.unop.ring from x.down)⟩
            rw [e.apply_symm_apply] }
      hom_inv_id := by ext x; rfl
      inv_hom_id := by ext x; rfl }) (by
    intro U V α
    ext x
    rfl)

def structureTransport :
    (twistedRestriction (p := p) e he he' h).obj (IntegralComparison.BigCrystallineCohomology.structureSheaf f') ≅ IntegralComparison.BigCrystallineCohomology.structureSheaf f := by
  letI := CrystallineTwistRestriction.twist_continuous (p := p) e he he' h
  letI := CrystallineTwistRestriction.twist_cocontinuous (p := p) e he he' h
  let R : ModuleCat.{u + 1} (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)) ⥤ ModuleCat.{u + 1} (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)) :=
    ModuleCat.restrictScalars (coefficientEquiv e).symm.toRingHom
  let P := (CrystallineBaseTwist.twist (p := p) e he h).op ⋙ IntegralComparison.BigCrystallineCohomology.largePresheaf f'
  let T := IntegralComparison.BigCrystallineSite.Object.topology (p := p) (J := J) (δ := δ) (f := f)
  letI : T.PreservesSheafification R := Sheaf.preservesSheafification_of_adjunction T
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u + 1}
      (coefficientEquiv e).symm).toAdjunction
  let G := SheafCoefficients.changeCoefficients.{u + 1, u, u + 1} T (coefficientEquiv e).symm
  let i₁ : (CrystallineTwistRestriction.restriction e he he' h).obj (IntegralComparison.BigCrystallineCohomology.structureSheaf f') ≅
      (presheafToSheaf T (ModuleCat.{u + 1} (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)))).obj P :=
    ((CrystallineBaseTwist.twist (p := p) e he h).pushforwardContinuousSheafificationCompatibility
      (ModuleCat.{u + 1} (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B))) IntegralComparison.BigCrystallineSite.Object.topology IntegralComparison.BigCrystallineSite.Object.topology).symm.app
        (IntegralComparison.BigCrystallineCohomology.largePresheaf f')
  let i₂ : G.obj ((presheafToSheaf T (ModuleCat.{u + 1} (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)))).obj P) ≅
      (presheafToSheaf T (ModuleCat.{u + 1} (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)))).obj (P ⋙ R) :=
    ((sheafComposeNatIso T R
      (sheafificationAdjunction T (ModuleCat.{u + 1} (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B))))
      (sheafificationAdjunction T (ModuleCat.{u + 1} (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B))))).app P).symm
  exact G.mapIso i₁ ≪≫ i₂ ≪≫
    (presheafToSheaf T (ModuleCat.{u + 1} (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)))).mapIso (presheafTransport e he h)

def constantTransport :
    (twistedRestriction (p := p) e he he' h).obj (IntegralComparison.BigCrystallineCohomology.constantUnit f') ≅ IntegralComparison.BigCrystallineCohomology.constantUnit f := by
  letI := CrystallineTwistRestriction.twist_continuous (p := p) e he he' h
  letI := CrystallineTwistRestriction.twist_cocontinuous (p := p) e he he' h
  let R : ModuleCat.{u + 1} (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)) ⥤ ModuleCat.{u + 1} (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)) :=
    ModuleCat.restrictScalars (coefficientEquiv e).symm.toRingHom
  let A := ModuleCat.of (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)) (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B))
  let T := IntegralComparison.BigCrystallineSite.Object.topology (p := p) (J := J) (δ := δ) (f := f)
  letI : T.PreservesSheafification R := Sheaf.preservesSheafification_of_adjunction T
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u + 1}
      (coefficientEquiv e).symm).toAdjunction
  let G := SheafCoefficients.changeCoefficients.{u + 1, u, u + 1} T (coefficientEquiv e).symm
  let i₁ : (CrystallineTwistRestriction.restriction e he he' h).obj (IntegralComparison.BigCrystallineCohomology.constantUnit f') ≅
      IntegralComparison.BigCrystallineCohomology.constantUnit f :=
    ((CrystallineBaseTwist.twist (p := p) e he h).pushforwardContinuousSheafificationCompatibility
      (ModuleCat.{u + 1} (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B))) IntegralComparison.BigCrystallineSite.Object.topology IntegralComparison.BigCrystallineSite.Object.topology).symm.app
        ((Functor.const _).obj A)
  let i₂ : G.obj (IntegralComparison.BigCrystallineCohomology.constantUnit f) ≅ (constantSheaf T (ModuleCat.{u + 1} (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)))).obj
      (R.obj A) := (constantCommuteCompose T R).app A
  exact G.mapIso i₁ ≪≫ i₂ ≪≫
    (constantSheaf T (ModuleCat.{u + 1} (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)))).mapIso
      (ModuleCat.restrictScalarsIsoOfEquiv (coefficientEquiv e).symm)

theorem twistedRestriction_map_smul
    (P : IntegralComparison.Crystalline.ExactRestriction.ModuleSheaf (p := p) (J := J) (δ := δ) f') (b : IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)) :
    (twistedRestriction e he he' h).map (b • 𝟙 P) =
      coefficientEquiv e b • 𝟙 ((twistedRestriction e he he' h).obj P) := by
  let F := CrystallineTwistRestriction.restriction (p := p) e he he' h
  let G := SheafCoefficients.changeCoefficients (IntegralComparison.BigCrystallineSite.Object.topology (p := p) (J := J) (δ := δ) (f := f))
    (coefficientEquiv e).symm
  change G.map (F.map (b • 𝟙 P)) = coefficientEquiv e b • 𝟙 (G.obj (F.obj P))
  have hF : F.map (b • 𝟙 P) = b • 𝟙 (F.obj P) := by
    rw [CategoryTheory.Functor.map_smul, CategoryTheory.Functor.map_id]
  exact (congrArg G.map hF).trans
    ((SheafCoefficients.changeCoefficients_map_smul _ _ (𝟙 (F.obj P)) b).trans
      (congrArg (fun a => coefficientEquiv e b • a) (G.map_id (F.obj P))))

def cohomologyMap (n : ℕ) : IntegralComparison.BigCrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f' n →ₛₗ[(coefficientEquiv e).toRingHom]
    IntegralComparison.BigCrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f n :=
  (IntegralComparison.Etale.Frobenius.extIsoCongr (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)) (constantTransport e he he' h)
    (structureTransport e he he' h) n).toLinearMap.comp
      (SemilinearExt.mapExt (coefficientEquiv e).toRingHom (twistedRestriction e he he' h)
        (twistedRestriction_map_smul e he he' h) (IntegralComparison.BigCrystallineCohomology.constantUnit f') (IntegralComparison.BigCrystallineCohomology.structureSheaf f') n)

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology
