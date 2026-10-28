import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CoefficientLimits
import OAI.NumberTheory.PadicHodge.GeometricComparison.CoefficientLimitCoordinates

/-! # Coefficient Limit -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CoefficientLimit.IntrinsicPadicCoefficientLimitComparison

noncomputable section

/-! The coefficient limit comparison in the actual p-adic and
large crystalline module universes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable (p : ℕ) [Fact p.Prime]
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "F" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.coefficients p

instance targetLimits : HasLimitsOfShape ℕᵒᵖ (ModuleCat.{2} R) :=
  ModuleCat.hasLimitsOfShape

variable (P : ℕᵒᵖ ⥤ ModuleCat.{0} ℤ_[p])
  (Q : ℕᵒᵖ ⥤ ModuleCat.{2} (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))))
  (e : P ⋙ Coefficient.IntrinsicPadicSmallQuotientTotal.coefficients p ≅ Q)

def iso : (F).obj (limit P) ≅ limit Q :=
  CoefficientLimit.CoefficientLimitComparison.iso.{0, 0, 1, 0, 3, 2} P Q F e

theorem hom_π (n : ℕᵒᵖ) : (iso p P Q e).hom ≫ limit.π Q n =
    (F).map (limit.π P n) ≫ e.hom.app n :=
  CoefficientLimit.CoefficientLimitComparison.hom_π.{0, 0, 1, 0, 3, 2} P Q F e n

variable {M : ModuleCat.{0} ℤ_[p]} (s : M ≅ limit P)

def sourceIso : (F).obj M ≅ limit Q :=
  CoefficientLimitCoordinates.CoefficientLimitSourceCoordinates.iso.{0, 0, 1, 0, 3, 2} P Q F e s

theorem sourceIso_hom_π (n : ℕᵒᵖ) : (sourceIso p P Q e s).hom ≫ limit.π Q n =
    (F).map (s.hom ≫ limit.π P n) ≫ e.hom.app n :=
  CoefficientLimitCoordinates.CoefficientLimitSourceCoordinates.hom_π.{0, 0, 1, 0, 3, 2} P Q F e s n

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CoefficientLimit.IntrinsicPadicCoefficientLimitComparison
