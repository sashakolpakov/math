import OAI.NumberTheory.PadicHodge.GeometricComparison.CochainQuotientTower
import OAI.NumberTheory.PadicHodge.IntegralComparison.SequentialKernelLimit

/-! # Cochain Quotient Limit -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CochainQuotientLimit.PrincipalCochainQuotient

noncomputable section

/-! The original compatible quotient cohomology is the categorical
inverse limit of the shifted tower used by crystalline levels. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v
variable (R : Type u) [CommRing R] (C : CochainComplex (ModuleCat.{v} R) ℕ) (r : R) (i : ℕ)

def shiftedDiagram : ℕᵒᵖ ⥤ ModuleCat.{v} R :=
  IntegralComparison.SequentialKernelLimit.diagram R (fun n => CochainQuotientCohomology.PrincipalCochainQuotient.cohomology R C r (n + 1) i)
    (fun n => CochainQuotientCohomology.PrincipalCochainQuotient.cohomologyTransition R C r i (n + 1) (n + 2) (by omega))

def compatibleLimitIso : ModuleCat.of R
    (AdicCohomology.AdicCohomologyLimit.compatible (fun n => CochainQuotientCohomology.PrincipalCochainQuotient.cohomology R C r n i) (CochainQuotientCohomology.PrincipalCochainQuotient.cohomologyTransition R C r i)) ≅
      limit (shiftedDiagram R C r i) :=
  (CochainQuotientTower.PrincipalCochainQuotient.shiftedCompatibleEquiv R C r i).toModuleIso ≪≫
    IntegralComparison.SequentialKernelLimit.limitIso R (fun n => CochainQuotientCohomology.PrincipalCochainQuotient.cohomology R C r (n + 1) i)
      (fun n => CochainQuotientCohomology.PrincipalCochainQuotient.cohomologyTransition R C r i (n + 1) (n + 2) (by omega))

theorem compatibleLimitIso_eval
    (x : AdicCohomology.AdicCohomologyLimit.compatible (fun n => CochainQuotientCohomology.PrincipalCochainQuotient.cohomology R C r n i) (CochainQuotientCohomology.PrincipalCochainQuotient.cohomologyTransition R C r i)) (n : ℕ) :
    limit.π (shiftedDiagram R C r i) (op n) ((compatibleLimitIso R C r i).hom x) = x.val (n + 1) := by
  have h := (IntegralComparison.SequentialKernelLimit.isLimit R (fun n => CochainQuotientCohomology.PrincipalCochainQuotient.cohomology R C r (n + 1) i)
    (fun n => CochainQuotientCohomology.PrincipalCochainQuotient.cohomologyTransition R C r i (n + 1) (n + 2) (by omega))).conePointUniqueUpToIso_hom_comp
      (limit.isLimit (shiftedDiagram R C r i)) (op n)
  exact ConcreteCategory.congr_hom h (CochainQuotientTower.PrincipalCochainQuotient.shiftedCompatibleEquiv R C r i x)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CochainQuotientLimit.PrincipalCochainQuotient
