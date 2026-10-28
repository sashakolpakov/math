import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HodgeFullness
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralAction

/-! # Hodge Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.HodgeIso.AbelianIntrinsicAdapter

noncomputable section

/-! The algebraized integral Hodge isomorphism belongs to the original
HilbertConstruction schemes. Its action equations hold as actual scheme morphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HodgeFullness.IntrinsicLinearMaps OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralAction.IntrinsicIntegralAction

variable {g h : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase) (B : HilbertConstruction.Abelian.Schemes.AbelianScheme h Foundations.Scheme.ProjectiveSpace.complexBase)
    (PA : Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom)
    (PB : Foundations.Scheme.SmoothProjective.ProjectivePresentation B.scheme.left B.scheme.hom)
    (e : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA) ≃ₗ[ℚ] Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B PB))
    (he : ComplexMultiplication.WeightOne.CM.IsHodgeMap (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA)) (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B PB)) e.toLinearMap)
    (hi : ComplexMultiplication.WeightOne.CM.IsHodgeMap (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B PB)) (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA)) e.symm.toLinearMap)
    (hΛ : ∀ v, v ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA) ↔ e v ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B PB))

def originalHodgeIso : A.scheme ≅ B.scheme :=
  (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A PA).symm ≪≫ Intrinsic.HodgeFullness.IntrinsicLinearMaps.nativeIntegralHodgeIso e he hi hΛ ≪≫ Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso B PB

instance originalHodgeIso_isMonHom : IsMonHom (originalHodgeIso A B PA PB e he hi hΛ).hom :=
  inferInstanceAs (IsMonHom ((Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A PA).inv ≫
    (Intrinsic.HodgeFullness.IntrinsicLinearMaps.nativeIntegralHodgeIso e he hi hΛ).hom ≫ (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso B PB).hom))

theorem originalHodgeIso_native_hom :
    (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A PA).hom ≫ (originalHodgeIso A B PA PB e he hi hΛ).hom ≫ (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso B PB).inv =
      (Intrinsic.HodgeFullness.IntrinsicLinearMaps.nativeIntegralHodgeIso e he hi hΛ).hom := by
  simp only [originalHodgeIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

theorem originalHodgeIso_rational :
    Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift ((Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A PA).hom ≫ (originalHodgeIso A B PA PB e he hi hΛ).hom ≫
      (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso B PB).inv) = e.toLinearMap :=
  (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_congr _ _ (originalHodgeIso_native_hom A B PA PB e he hi hΛ)).trans
    (Intrinsic.HodgeFullness.IntrinsicLinearMaps.nativeIntegralHodgeIso_rational e he hi hΛ)

theorem originalHodgeIso_intertwines {R : Type*} [CommRing R]
    (ρ : ActionData.IntegralAction R A) (σ : ActionData.IntegralAction R B)
    (hact : ∀ a : R, e.toLinearMap.comp (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (Intrinsic.IntegralAction.IntrinsicIntegralAction.nativeMap A PA ρ a)) =
      (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (Intrinsic.IntegralAction.IntrinsicIntegralAction.nativeMap B PB σ a)).comp e.toLinearMap) (a : R) :
    ρ.map a ≫ (originalHodgeIso A B PA PB e he hi hΛ).hom =
      (originalHodgeIso A B PA PB e he hi hΛ).hom ≫ σ.map a := by
  have hn := Intrinsic.HodgeFullness.IntrinsicLinearMaps.nativeIntegralHodgeIso_intertwines e he hi hΛ (Intrinsic.IntegralAction.IntrinsicIntegralAction.nativeMap A PA ρ a) (Intrinsic.IntegralAction.IntrinsicIntegralAction.nativeMap B PB σ a) (hact a)
  have ht := congrArg (fun f => (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A PA).inv ≫ f ≫ (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso B PB).hom) hn
  simpa only [originalHodgeIso, Iso.trans_hom, Iso.symm_hom, Intrinsic.IntegralAction.IntrinsicIntegralAction.nativeMap, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id] using ht

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.HodgeIso.AbelianIntrinsicAdapter
