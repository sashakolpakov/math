import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyNaturality
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PolarizedComposites
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Product.ClassPairingNaturality

/-! # Intrinsic Homology Power -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntrinsicHomologyPower

noncomputable section

/-! Actual multiplication maps act by their integer multiplier on native
rational periods and first singular homology. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Product.ClassPairingNaturality OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyNaturality.IntrinsicRationalPeriods

variable {A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}

theorem nativeRationalLift_mul (f g : A.toOver ⟶ B.toOver) [IsMonHom f] [IsMonHom g] :
    AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (f * g) = AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f + AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift g := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun (AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicLinearMaps.linearLift_add f g) x.val

theorem nativeRationalLift_one : AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (1 : A.toOver ⟶ B.toOver) = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun (AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicLinearMaps.linearLift_zero A B) x.val

theorem nativeRationalLift_pow (f : A.toOver ⟶ B.toOver) [IsMonHom f] (n : ℕ) :
    AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (f ^ n) = n • AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f := by
  induction n with
  | zero => simp only [pow_zero, nativeRationalLift_one, zero_nsmul]
  | succ n hn => simp only [pow_succ, nativeRationalLift_mul, hn, succ_nsmul]

theorem nativePointHomology_pow (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ)
    (x : AbelianModuli.ReferenceFamily.HomologyCrossPairing.firstHomology (Betti.Scheme.schemePointSpace A.toOver)) :
    HomologicalComplex.homologyMap
      ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains ℚ).map
        (TopCat.ofHom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous ((𝟙 A.toOver) ^ n)))) 1 x = n • x := by
  obtain ⟨v, rfl⟩ := (AbelianModuli.ReferenceFamily.Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods A).surjective x
  have h := AbelianModuli.ReferenceFamily.Intrinsic.HomologyNaturality.IntrinsicRationalPeriods.nativeHomologyPeriods_naturality ((𝟙 A.toOver) ^ n) v
  rw [nativeRationalLift_pow, AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_id, LinearMap.smul_apply,
    LinearMap.id_apply, map_nsmul] at h
  exact h.symm

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntrinsicHomologyPower
