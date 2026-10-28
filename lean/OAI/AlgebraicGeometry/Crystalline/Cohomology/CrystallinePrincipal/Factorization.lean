import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Opens

/-! # Factorization -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Factorization.CrystallinePrincipalFactorization

noncomputable section

/-!
# Factorization through actual principal-open crystalline objects

A native crystalline map factors through a principal open whenever the
ambient coefficient becomes a unit. The factor preserves the actual
divided powers by the localized PD universal property. Principal-open
projections are monomorphisms in the native crystalline category.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k)))
  {P Q : Site.Object p k X} (f : P ⟶ Q) (s : Q.thickening.ring)
  (hs : IsUnit (f.ambientMap s))

def ambientLift : Localization.Away s →ₐ[WittVector p k] P.thickening.ring :=
  IsLocalization.Away.liftAlgHom s hs

theorem ambientLift_comp : (ambientLift p k X f s hs).toRingHom.comp
    (algebraMap Q.thickening.ring (Localization.Away s)) = f.ambientMap.toRingHom :=
  IsLocalization.Away.lift_comp s hs

include hs in
theorem reduced_unit : IsUnit (f.reducedMap (Q.thickening.reduction s)) := by
  have hu := hs.map P.thickening.reduction
  rw [f.reduction_comm] at hu
  exact hu

def reducedLift : Localization.Away (Q.thickening.reduction s) →ₐ[k] P.residueRing :=
  IsLocalization.Away.liftAlgHom (Q.thickening.reduction s) (reduced_unit p k X f s hs)

theorem reducedLift_comp : (reducedLift p k X f s hs).toRingHom.comp
    (algebraMap Q.residueRing (Localization.Away (Q.thickening.reduction s))) = f.reducedMap.toRingHom :=
  IsLocalization.Away.lift_comp (Q.thickening.reduction s) (reduced_unit p k X f s hs)

theorem reduction_comm (z : Localization.Away s) :
    P.thickening.reduction (ambientLift p k X f s hs z) =
      reducedLift p k X f s hs (LocalizationReductionKernel.LocalizationReduction.map Q.thickening.ring Q.residueRing Q.thickening.reduction s z) := by
  have he : P.thickening.reduction.comp (ambientLift p k X f s hs).toRingHom =
      (reducedLift p k X f s hs).toRingHom.comp
        (LocalizationReductionKernel.LocalizationReduction.map Q.thickening.ring Q.residueRing Q.thickening.reduction s) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers s)
    ext x
    change P.thickening.reduction (ambientLift p k X f s hs
      (algebraMap Q.thickening.ring (Localization.Away s) x)) =
        reducedLift p k X f s hs (LocalizationReductionKernel.LocalizationReduction.map Q.thickening.ring Q.residueRing Q.thickening.reduction s
          (algebraMap Q.thickening.ring (Localization.Away s) x))
    rw [show ambientLift p k X f s hs (algebraMap Q.thickening.ring (Localization.Away s) x) = f.ambientMap x from
      RingHom.congr_fun (ambientLift_comp p k X f s hs) x,
      LocalizationReductionKernel.LocalizationReduction.map_algebraMap,
      show reducedLift p k X f s hs (algebraMap Q.residueRing (Localization.Away (Q.thickening.reduction s))
        (Q.thickening.reduction x)) = f.reducedMap (Q.thickening.reduction x) from
          RingHom.congr_fun (reducedLift_comp p k X f s hs) (Q.thickening.reduction x)]
    exact f.reduction_comm x
  exact RingHom.congr_fun he z

theorem ambientLift_isDPMorphism :
    DividedPowers.IsDPMorphism (Opens.CrystallinePrincipalOpens.object p k X Q s).thickening.dividedPowers
      P.thickening.dividedPowers (ambientLift p k X f s hs).toRingHom := by
  have hb : DividedPowers.IsDPMorphism Q.thickening.dividedPowers P.thickening.dividedPowers
      ((ambientLift p k X f s hs).toRingHom.comp (algebraMap Q.thickening.ring (Localization.Away s))) := by
    rw [ambientLift_comp]
    exact f.dp_comp
  have hd := PD.LocalizationUniversal.PDLocalizationUniversal.map_isDPMorphism Q.thickening.ring (Localization.Away s)
    (Submonoid.powers s) (RingHom.ker Q.thickening.reduction) Q.thickening.dividedPowers
    P.thickening.ring (RingHom.ker P.thickening.reduction) P.thickening.dividedPowers
    (ambientLift p k X f s hs).toRingHom hb
  exact hd.comp _ (LocalizedPD.LocalizedPDThickening.identity_inverse_isDPMorphism p k Q.residueRing Q.thickening s)

def lift : P ⟶ Opens.CrystallinePrincipalOpens.object p k X Q s where
  ambientMap := ambientLift p k X f s hs
  reducedMap := reducedLift p k X f s hs
  reduction_comm := CrystallinePrincipalFactorization.reduction_comm p k X f s hs
  over_X := by
    change Spec.map (CommRingCat.ofHom (reducedLift p k X f s hs).toRingHom) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap Q.residueRing (Localization.Away (Q.thickening.reduction s)))) ≫
        Q.immersion) = P.immersion
    rw [← Category.assoc, ← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom ((reducedLift p k X f s hs).toRingHom.comp
      (algebraMap Q.residueRing (Localization.Away (Q.thickening.reduction s))))) ≫ Q.immersion = P.immersion
    rw [reducedLift_comp]
    exact f.over_X
  dp_comp := ambientLift_isDPMorphism p k X f s hs

theorem lift_projection : lift p k X f s hs ≫ Opens.CrystallinePrincipalOpens.projection p k X Q s = f := by
  apply Site.Object.Hom.ext
  · exact AlgHom.ext (RingHom.congr_fun (reducedLift_comp p k X f s hs))
  · exact AlgHom.ext (RingHom.congr_fun (ambientLift_comp p k X f s hs))

instance projection_mono (Q : Site.Object p k X) (s : Q.thickening.ring) :
    Mono (Opens.CrystallinePrincipalOpens.projection p k X Q s) where
  right_cancellation {Z} g h hgh := by
    apply Site.Object.Hom.ext
    · have he := congrArg (fun m : Z ⟶ Q => m.reducedMap.toRingHom) hgh
      change g.reducedMap.toRingHom.comp
        (algebraMap Q.residueRing (Localization.Away (Q.thickening.reduction s))) =
          h.reducedMap.toRingHom.comp
            (algebraMap Q.residueRing (Localization.Away (Q.thickening.reduction s))) at he
      exact AlgHom.ext (RingHom.congr_fun
        (IsLocalization.ringHom_ext (S := Localization.Away (Q.thickening.reduction s))
          (Submonoid.powers (Q.thickening.reduction s)) he))
    · have he := congrArg (fun m : Z ⟶ Q => m.ambientMap.toRingHom) hgh
      change g.ambientMap.toRingHom.comp (algebraMap Q.thickening.ring (Localization.Away s)) =
        h.ambientMap.toRingHom.comp (algebraMap Q.thickening.ring (Localization.Away s)) at he
      exact AlgHom.ext (RingHom.congr_fun
        (IsLocalization.ringHom_ext (S := Localization.Away s) (Submonoid.powers s) he))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Factorization.CrystallinePrincipalFactorization
