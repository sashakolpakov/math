import OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistNaturality
import OAI.NumberTheory.PadicHodge.PeriodInvariants.ChangedCoefficientSheafification
import OAI.NumberTheory.PadicHodge.PeriodInvariants.ConstantCoefficientCoherence

/-! # Crystalline Twist Generators -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistGenerators

noncomputable section

/-!
# Presheaf generators under the actual semilinear crystalline twist

The coefficient-change comparison sends each original structure-presheaf
generator through the prescribed inverse presheaf identification. This
characterizes the twist map used in crystalline Frobenius.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Functor _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology
  CrystallineBaseTwist CrystallineTwistRestriction CrystallineTwistCohomology

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
variable {X : Scheme.{u}} {f f' : X ⟶ Spec (CommRingCat.of B)}

abbrev constantPresheaf (f₀ : X ⟶ Spec (CommRingCat.of B)) :
    (IntegralComparison.BigCrystallineSite.Object p B J δ f₀)ᵒᵖ ⥤ ModuleCat.{u + 1} (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)) :=
  (Functor.const _).obj (ModuleCat.of (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)) (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)))

variable (e : B ≃+* B) (he : DividedPowers.IsDPMorphism δ δ e.toRingHom)
  (he' : DividedPowers.IsDPMorphism δ δ e.symm.toRingHom)
  (h : f' = f ≫ Spec.map (CommRingCat.ofHom e.toRingHom))

theorem structureTransport_generator :
    toSheafify IntegralComparison.BigCrystallineSite.Object.topology (IntegralComparison.BigCrystallineCohomology.largePresheaf f) ≫
        (CrystallineTwistCohomology.structureTransport (p := p) e he he' h).inv.hom =
      (CrystallineTwistCohomology.presheafTransport e he h).inv ≫
        whiskerRight (whiskerLeft (CrystallineBaseTwist.twist (p := p) e he h).op (toSheafify IntegralComparison.BigCrystallineSite.Object.topology (IntegralComparison.BigCrystallineCohomology.largePresheaf f')))
          (ModuleCat.restrictScalars (CrystallineTwistCohomology.coefficientEquiv e).symm.toRingHom) := by
  let := CrystallineTwistRestriction.twist_continuous (p := p) e he he' h
  let := CrystallineTwistRestriction.twist_cocontinuous (p := p) e he he' h
  let R : ModuleCat.{u + 1} (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)) ⥤ ModuleCat.{u + 1} (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)) :=
    ModuleCat.restrictScalars (CrystallineTwistCohomology.coefficientEquiv e).symm.toRingHom
  let T := IntegralComparison.BigCrystallineSite.Object.topology (p := p) (J := J) (δ := δ) (f := f)
  let : T.PreservesSheafification R := Sheaf.preservesSheafification_of_adjunction T
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u + 1} (CrystallineTwistCohomology.coefficientEquiv e).symm).toAdjunction
  exact ChangedCoefficientSheafification.transported_generator T IntegralComparison.BigCrystallineSite.Object.topology
    (CrystallineBaseTwist.twist (p := p) e he h) R (IntegralComparison.BigCrystallineCohomology.largePresheaf f') (IntegralComparison.BigCrystallineCohomology.largePresheaf f)
    (CrystallineTwistCohomology.presheafTransport e he h)

def constantPresheafTransport :
    ((CrystallineBaseTwist.twist (p := p) e he h).op ⋙ constantPresheaf f') ⋙
        ModuleCat.restrictScalars (CrystallineTwistCohomology.coefficientEquiv e).symm.toRingHom ≅ constantPresheaf f :=
  constComp (IntegralComparison.BigCrystallineSite.Object p B J δ f)ᵒᵖ (ModuleCat.of (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)) (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)))
      (ModuleCat.restrictScalars (CrystallineTwistCohomology.coefficientEquiv e).symm.toRingHom) ≪≫
    (Functor.const _).mapIso (ModuleCat.restrictScalarsIsoOfEquiv (CrystallineTwistCohomology.coefficientEquiv e).symm)

theorem constantTransport_eq :
    letI := CrystallineTwistRestriction.twist_continuous (p := p) e he he' h
    letI := CrystallineTwistRestriction.twist_cocontinuous (p := p) e he he' h
    let R : ModuleCat.{u + 1} (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)) ⥤ ModuleCat.{u + 1} (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)) :=
      ModuleCat.restrictScalars (CrystallineTwistCohomology.coefficientEquiv e).symm.toRingHom
    let T := IntegralComparison.BigCrystallineSite.Object.topology (p := p) (J := J) (δ := δ) (f := f)
    letI : T.PreservesSheafification R := Sheaf.preservesSheafification_of_adjunction T
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u + 1} (CrystallineTwistCohomology.coefficientEquiv e).symm).toAdjunction
    CrystallineTwistCohomology.constantTransport (p := p) e he he' h =
      ChangedCoefficientSheafification.transported T IntegralComparison.BigCrystallineSite.Object.topology
        (CrystallineBaseTwist.twist (p := p) e he h) R (constantPresheaf f') (constantPresheaf f)
        (constantPresheafTransport e he h) := by
  let := CrystallineTwistRestriction.twist_continuous (p := p) e he he' h
  let := CrystallineTwistRestriction.twist_cocontinuous (p := p) e he he' h
  let R : ModuleCat.{u + 1} (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)) ⥤ ModuleCat.{u + 1} (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)) :=
    ModuleCat.restrictScalars (CrystallineTwistCohomology.coefficientEquiv e).symm.toRingHom
  let T := IntegralComparison.BigCrystallineSite.Object.topology (p := p) (J := J) (δ := δ) (f := f)
  let : T.PreservesSheafification R := Sheaf.preservesSheafification_of_adjunction T
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u + 1} (CrystallineTwistCohomology.coefficientEquiv e).symm).toAdjunction
  let A := ModuleCat.of (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)) (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B))
  let S := presheafToSheaf T (ModuleCat.{u + 1} (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)))
  let i₁ := (sheafCompose T R).mapIso
    (SheafificationCoherence.transport T IntegralComparison.BigCrystallineSite.Object.topology (CrystallineBaseTwist.twist (p := p) e he h) (constantPresheaf f'))
  let i₂ := ((sheafComposeNatIso T R (sheafificationAdjunction T (ModuleCat.{u + 1} (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B))))
    (sheafificationAdjunction T (ModuleCat.{u + 1} (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B))))).app (constantPresheaf f)).symm
  let a := constComp (IntegralComparison.BigCrystallineSite.Object p B J δ f)ᵒᵖ A R
  let b := (Functor.const (IntegralComparison.BigCrystallineSite.Object p B J δ f)ᵒᵖ).mapIso
    (ModuleCat.restrictScalarsIsoOfEquiv (CrystallineTwistCohomology.coefficientEquiv e).symm)
  change i₁ ≪≫ (i₂ ≪≫ S.mapIso a) ≪≫ S.mapIso b = (i₁ ≪≫ i₂) ≪≫ S.mapIso (a ≪≫ b)
  rw [Functor.mapIso_trans]
  simp only [Iso.trans_assoc]

theorem constantTransport_generator :
    toSheafify IntegralComparison.BigCrystallineSite.Object.topology (constantPresheaf f) ≫
        (CrystallineTwistCohomology.constantTransport (p := p) e he he' h).inv.hom =
      (constantPresheafTransport e he h).inv ≫
        whiskerRight (whiskerLeft (CrystallineBaseTwist.twist (p := p) e he h).op
          (toSheafify IntegralComparison.BigCrystallineSite.Object.topology (constantPresheaf f')))
          (ModuleCat.restrictScalars (CrystallineTwistCohomology.coefficientEquiv e).symm.toRingHom) := by
  let := CrystallineTwistRestriction.twist_continuous (p := p) e he he' h
  let := CrystallineTwistRestriction.twist_cocontinuous (p := p) e he he' h
  let R : ModuleCat.{u + 1} (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)) ⥤ ModuleCat.{u + 1} (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)) :=
    ModuleCat.restrictScalars (CrystallineTwistCohomology.coefficientEquiv e).symm.toRingHom
  let T := IntegralComparison.BigCrystallineSite.Object.topology (p := p) (J := J) (δ := δ) (f := f)
  let : T.PreservesSheafification R := Sheaf.preservesSheafification_of_adjunction T
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u + 1} (CrystallineTwistCohomology.coefficientEquiv e).symm).toAdjunction
  exact (congrArg (fun i => toSheafify T (constantPresheaf f) ≫ i.inv.hom)
    (constantTransport_eq e he he' h)).trans
      (ChangedCoefficientSheafification.transported_generator T IntegralComparison.BigCrystallineSite.Object.topology
        (CrystallineBaseTwist.twist (p := p) e he h) R (constantPresheaf f') (constantPresheaf f)
        (constantPresheafTransport e he h))

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistGenerators
