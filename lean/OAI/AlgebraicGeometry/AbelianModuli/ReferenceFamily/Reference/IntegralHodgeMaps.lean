import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.HodgeScalarIsogenies
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralAction

/-! # Integral Hodge Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.IntegralHodgeMaps.AbelianIntrinsicAdapter

noncomputable section

/-! Exact integral Hodge maps descend to the original HilbertConstruction abelian
schemes. Scalar complements and integral-action equations are proved
on those original schemes through their faithful rational periods. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.HodgeScalarIsogenies.IntrinsicLinearMaps OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralAction.IntrinsicIntegralAction

variable {g h : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase) (B : HilbertConstruction.Abelian.Schemes.AbelianScheme h Foundations.Scheme.ProjectiveSpace.complexBase)
    (PA : Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom)
    (PB : Foundations.Scheme.SmoothProjective.ProjectivePresentation B.scheme.left B.scheme.hom)
    (f : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA) →ₗ[ℚ] Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B PB))
    (hf : ComplexMultiplication.WeightOne.CM.IsHodgeMap (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA))
      (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B PB)) f)
    (hΛ : ∀ x ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA), f x ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B PB))

def originalIntegralHodgeMap : A.scheme ⟶ B.scheme :=
  (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A PA).inv ≫ Intrinsic.HodgeFullness.IntrinsicLinearMaps.nativeHodgeDescend f hf hΛ ≫ (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso B PB).hom

instance originalIntegralHodgeMap_isMonHom : IsMonHom (originalIntegralHodgeMap A B PA PB f hf hΛ) :=
  inferInstanceAs (IsMonHom
    ((Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A PA).inv ≫ Intrinsic.HodgeFullness.IntrinsicLinearMaps.nativeHodgeDescend f hf hΛ ≫ (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso B PB).hom))

theorem originalIntegralHodgeMap_native :
    (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A PA).hom ≫ originalIntegralHodgeMap A B PA PB f hf hΛ ≫ (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso B PB).inv =
      Intrinsic.HodgeFullness.IntrinsicLinearMaps.nativeHodgeDescend f hf hΛ := by
  simp only [originalIntegralHodgeMap, Category.assoc, Iso.hom_inv_id_assoc,
    Iso.hom_inv_id, Category.comp_id]

theorem originalIntegralHodgeMap_rational :
    Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift ((Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A PA).hom ≫ originalIntegralHodgeMap A B PA PB f hf hΛ ≫
      (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso B PB).inv) = f :=
  (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_congr _ _ (originalIntegralHodgeMap_native A B PA PB f hf hΛ)).trans
    (Intrinsic.HodgeFullness.IntrinsicLinearMaps.rationalLift_nativeHodgeDescend f hf hΛ)

theorem originalIntegralHodgeMap_intertwines {R : Type*} [CommRing R]
    (ρ : ActionData.IntegralAction R A) (σ : ActionData.IntegralAction R B)
    (hact : ∀ a, f.comp (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (Intrinsic.IntegralAction.IntrinsicIntegralAction.nativeMap A PA ρ a)) =
      (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (Intrinsic.IntegralAction.IntrinsicIntegralAction.nativeMap B PB σ a)).comp f) (a : R) :
    ρ.map a ≫ originalIntegralHodgeMap A B PA PB f hf hΛ =
      originalIntegralHodgeMap A B PA PB f hf hΛ ≫ σ.map a := by
  have hn := Integral.HodgeScalarIsogenies.IntrinsicLinearMaps.nativeIntegralHodgeMap_intertwines f hf hΛ
    (Intrinsic.IntegralAction.IntrinsicIntegralAction.nativeMap A PA ρ a) (Intrinsic.IntegralAction.IntrinsicIntegralAction.nativeMap B PB σ a) (hact a)
  have ht := congrArg (fun m => (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A PA).inv ≫ m ≫ (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso B PB).hom) hn
  simpa only [originalIntegralHodgeMap, Intrinsic.IntegralAction.IntrinsicIntegralAction.nativeMap, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id] using ht

variable (v : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B PB) →ₗ[ℚ] Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA))
    (hv : ComplexMultiplication.WeightOne.CM.IsHodgeMap (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B PB))
      (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA)) v)
    (hΛv : ∀ x ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B PB), v x ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA))
    (n : ℕ)

theorem originalIntegralHodgeMaps_scalar_composition
    (hfv : v.comp f = n • (LinearMap.id : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA) →ₗ[ℚ] Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA))) :
    originalIntegralHodgeMap A B PA PB f hf hΛ ≫ originalIntegralHodgeMap B A PB PA v hv hΛv =
      (𝟙 A.scheme) ^ n := by
  have hc := Integral.HodgeScalarIsogenies.IntrinsicLinearMaps.nativeIntegralHodgeMaps_scalar_composition f v hf hv hΛ hΛv n hfv
  calc
    _ = (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A PA).inv ≫
        (Intrinsic.HodgeFullness.IntrinsicLinearMaps.nativeHodgeDescend f hf hΛ ≫ Intrinsic.HodgeFullness.IntrinsicLinearMaps.nativeHodgeDescend v hv hΛv) ≫ (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A PA).hom := by
      simp only [originalIntegralHodgeMap, Category.assoc, Iso.hom_inv_id_assoc]
    _ = (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A PA).inv ≫ ((𝟙 (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA).toOver) ^ n) ≫ (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A PA).hom := by rw [hc]
    _ = (𝟙 A.scheme) ^ n := by
      rw [MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Iso.inv_hom_id]

include hv hΛv in
theorem originalIntegralHodgeMap_finite_etale
    (hn : 0 < n)
    (hfv : v.comp f = n • (LinearMap.id : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA) →ₗ[ℚ] Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA)))
    (hvf : f.comp v = n • (LinearMap.id : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B PB) →ₗ[ℚ] Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B PB))) :
    IsFinite (originalIntegralHodgeMap A B PA PB f hf hΛ).left ∧
      Etale (originalIntegralHodgeMap A B PA PB f hf hΛ).left ∧
      Surjective (originalIntegralHodgeMap A B PA PB f hf hΛ).left := by
  have hm := Integral.HodgeScalarIsogenies.IntrinsicLinearMaps.nativeIntegralHodgeMaps_both_finite_etale f v hf hv hΛ hΛv n hn hfv hvf
  let : IsFinite (Intrinsic.HodgeFullness.IntrinsicLinearMaps.nativeHodgeDescend f hf hΛ).left := hm.1
  let : Etale (Intrinsic.HodgeFullness.IntrinsicLinearMaps.nativeHodgeDescend f hf hΛ).left := hm.2.1
  let : Surjective (Intrinsic.HodgeFullness.IntrinsicLinearMaps.nativeHodgeDescend f hf hΛ).left := hm.2.2.1
  let : IsIso (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A PA).inv.left :=
    (Over.forget Foundations.Scheme.ProjectiveSpace.complexBase).map_isIso (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A PA).inv
  let : IsIso (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso B PB).hom.left :=
    (Over.forget Foundations.Scheme.ProjectiveSpace.complexBase).map_isIso (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso B PB).hom
  change IsFinite ((Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A PA).inv.left ≫
      (Intrinsic.HodgeFullness.IntrinsicLinearMaps.nativeHodgeDescend f hf hΛ).left ≫ (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso B PB).hom.left) ∧
    Etale ((Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A PA).inv.left ≫
      (Intrinsic.HodgeFullness.IntrinsicLinearMaps.nativeHodgeDescend f hf hΛ).left ≫ (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso B PB).hom.left) ∧
    Surjective ((Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A PA).inv.left ≫
      (Intrinsic.HodgeFullness.IntrinsicLinearMaps.nativeHodgeDescend f hf hΛ).left ≫ (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso B PB).hom.left)
  exact ⟨inferInstance, inferInstance, inferInstance⟩

def originalIntegralHodgeIsogeny
    (hn : 0 < n)
    (hfv : v.comp f = n • (LinearMap.id : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA) →ₗ[ℚ] Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA)))
    (hvf : f.comp v = n • (LinearMap.id : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B PB) →ₗ[ℚ] Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B PB))) :
    HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B := by
  have hm := originalIntegralHodgeMap_finite_etale A B PA PB f hf hΛ v hv hΛv n hn hfv hvf
  let : Etale (originalIntegralHodgeMap A B PA PB f hf hΛ).left := hm.2.1
  exact {
    hom := originalIntegralHodgeMap A B PA PB f hf hΛ
    preservesGroup := inferInstance
    finite := hm.1
    flat := inferInstance
    surjective := hm.2.2 }

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.IntegralHodgeMaps.AbelianIntrinsicAdapter
