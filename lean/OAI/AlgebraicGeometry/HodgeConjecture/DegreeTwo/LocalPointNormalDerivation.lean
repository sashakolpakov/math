import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalDerivation
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.PrincipalSmoothLocalization
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothAffineCharts

/-! # Local Point Normal Derivation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LocalPointNormalDerivation.Constructions

noncomputable section

/-!
# DegreeTwo: normalized point derivations from local divisor smoothness

A normalized normal derivation on the ambient principal localization
restricts to the original algebra, preserving the actual divisor parameter.
-/

variable {S : Type*} [CommRing S] [IsDomain S] [Algebra ℂ S] [Algebra.Smooth ℂ S]

/-- Smoothness of a principal open of the hypersurface supplies a
normalized point derivation on the original ambient algebra. -/
theorem exists_local_point_normal_derivation (p b : S) (hp : p ≠ 0)
    [Algebra.Smooth ℂ (Localization.Away (Ideal.Quotient.mk (Ideal.span {p}) b))]
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) (hxp : x p = 0) (hxb : x b ≠ 0) :
    letI := x.toRingHom.toAlgebra
    ∃ δ : Derivation ℂ S ℂ, δ p = 1 := by
  let := x.toRingHom.toAlgebra
  let T := Localization.Away b
  let y := Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint x b hxb
  let : Algebra T ℂ := y.toRingHom.toAlgebra
  let : IsScalarTower ℂ T ℂ := IsScalarTower.of_algHom y
  let : IsScalarTower S T ℂ := IsScalarTower.of_algebraMap_eq (fun a =>
    (DFunLike.congr_fun (Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint_comp x b hxb) a).symm)
  have hb : b ≠ 0 := fun h => hxb (h ▸ map_zero x)
  let : IsDomain T := Localization.Away.isDomain hb
  let : Algebra.Smooth ℂ T := Algebra.Smooth.comp ℂ S T
  let p' := algebraMap S T p
  have hp' : p' ≠ 0 := (map_ne_zero_iff _ (IsLocalization.injective T
    (powers_le_nonZeroDivisors_of_noZeroDivisors hb))).mpr hp
  let : Algebra.Smooth ℂ (T ⧸ Ideal.span {p'}) := PrincipalSmoothLocalization.Constructions.principal_quotient_localization_smooth ℂ S p b
  have hyp : y p' = 0 := (DFunLike.congr_fun (Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint_comp x b hxb) p).trans hxp
  obtain ⟨ε, hε⟩ := NormalDerivation.Constructions.exists_point_normal_derivation ℂ T ℂ p' hp' hyp
  exact ⟨ε.compAlgebraMap S, hε⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LocalPointNormalDerivation.Constructions
