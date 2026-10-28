import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.LocalLifts

/-! # Stalk Lifts -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.StalkLifts

noncomputable section

/-! On an affine scheme, actual infinitesimal stalk lifts are exactly
the infinitesimal lifts of the global coordinate ring. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace AffineStalkLifts

variable {X : Scheme.{0}} [IsAffine X] {C : CommRingCat.{0}} [IsLocalRing C]
  (J : Ideal C) (hJ : J ^ 2 = ⊥) {x : X} (e : X.presheaf.stalk x ⟶ C) [IsLocalHom e.hom]

def globalMap := e.hom.comp (X.presheaf.Γgerm x).hom

def toGlobal : AbelianScheme.TorsionQuotient.LocalLifts.LocalSchemeLifts.Lifts J hJ e →ₗ[C]
    AbelianScheme.TorsionQuotient.SquareZero.SquareZeroLifts.Lift J hJ (globalMap e) :=
  AbelianScheme.TorsionQuotient.SquareZero.SquareZeroLifts.Lift.comap (X.presheaf.Γgerm x).hom

def point (v : AbelianScheme.TorsionQuotient.SquareZero.SquareZeroLifts.Lift J hJ (globalMap e)) : Spec C ⟶ X :=
  Spec.map (CommRingCat.ofHom v.hom) ≫ X.isoSpec.inv

omit [IsLocalRing C] [IsLocalHom e.hom] in
theorem point_toGlobal (v : AbelianScheme.TorsionQuotient.LocalLifts.LocalSchemeLifts.Lifts J hJ e) :
    point J hJ e (toGlobal J hJ e v) = AbelianScheme.TorsionQuotient.LocalLifts.LocalSchemeLifts.toPoint J hJ e v := by
  calc
    point J hJ e (toGlobal J hJ e v) =
        (Spec.map (CommRingCat.ofHom v.hom) ≫ Spec.map (X.presheaf.Γgerm x)) ≫ X.isoSpec.inv :=
      congrArg (fun q => q ≫ X.isoSpec.inv)
        (Spec.map_comp (X.presheaf.Γgerm x) (CommRingCat.ofHom v.hom))
    _ = (Spec.map (CommRingCat.ofHom v.hom) ≫
        (X.fromSpecStalk x ≫ X.toSpecΓ)) ≫ X.isoSpec.inv :=
      congrArg (fun q => (Spec.map (CommRingCat.ofHom v.hom) ≫ q) ≫ X.isoSpec.inv)
        (Scheme.fromSpecStalk_toSpecΓ X x).symm
    _ = AbelianScheme.TorsionQuotient.LocalLifts.LocalSchemeLifts.toPoint J hJ e v := by
      rw [Category.assoc, Category.assoc, Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]
      rfl

omit [IsLocalRing C] [IsLocalHom e.hom] in
theorem point_injective : Function.Injective (point J hJ e) := by
  intro v w h
  apply AbelianScheme.TorsionQuotient.SquareZero.SquareZeroLifts.Lift.ext
  have h' := (cancel_mono X.isoSpec.inv).mp h
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h')

omit [IsLocalRing C] [IsLocalHom e.hom] in
theorem point_reduction (v : AbelianScheme.TorsionQuotient.SquareZero.SquareZeroLifts.Lift J hJ (globalMap e)) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ point J hJ e v =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ AbelianScheme.TorsionQuotient.LocalLifts.LocalSchemeLifts.ofGerm X x e := by
  have heq : CommRingCat.ofHom v.hom ≫ CommRingCat.ofHom (Ideal.Quotient.mk J) =
      CommRingCat.ofHom (globalMap e) ≫ CommRingCat.ofHom (Ideal.Quotient.mk J) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro b
    exact Ideal.Quotient.eq.mpr (v.congruent b)
  have hz := point_toGlobal J hJ e 0
  change point J hJ e 0 = AbelianScheme.TorsionQuotient.LocalLifts.LocalSchemeLifts.ofGerm X x e at hz
  rw [← hz]
  change _ ≫ (Spec.map (CommRingCat.ofHom v.hom) ≫ X.isoSpec.inv) =
    _ ≫ (Spec.map (CommRingCat.ofHom (globalMap e)) ≫ X.isoSpec.inv)
  rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc, heq]

theorem toGlobal_bijective : Function.Bijective (toGlobal J hJ e) := by
  constructor
  · intro v w h
    apply AbelianScheme.TorsionQuotient.LocalLifts.LocalSchemeLifts.toPoint_injective J hJ e
    exact (point_toGlobal J hJ e v).symm.trans
      ((congrArg (point J hJ e) h).trans (point_toGlobal J hJ e w))
  · intro w
    obtain ⟨v, hv⟩ := AbelianScheme.TorsionQuotient.LocalLifts.LocalSchemeLifts.exists_stalkLift J hJ e (point J hJ e w)
      (point_reduction J hJ e w)
    exact ⟨v, point_injective J hJ e ((point_toGlobal J hJ e v).trans hv)⟩

def equiv : AbelianScheme.TorsionQuotient.LocalLifts.LocalSchemeLifts.Lifts J hJ e ≃ₗ[C] AbelianScheme.TorsionQuotient.SquareZero.SquareZeroLifts.Lift J hJ (globalMap e) :=
  LinearEquiv.ofBijective (toGlobal J hJ e) (toGlobal_bijective J hJ e)

end AffineStalkLifts

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.StalkLifts
