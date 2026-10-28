import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.LocalDivisor
import OAI.AlgebraicGeometry.CycleClass.Thom.SemilocalDivisorNorm

/-! # Normalized Branch Order -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.NormalizedBranchOrder.Constructions.NormalizationLocal

noncomputable section

/-!
# ThomClass: actual divisor orders on singular supports as finite branch sums

The normalization of a codimension-one stalk is a finite Dedekind
algebra in the original function field. Its actual finite set of normal
branches, their residue degrees, and their rational orders recover the
original Scheme.ord. The input local ring may be singular and have
several branches after normalization.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory IsDedekindDomain _root_.Order

variable (X : Scheme) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
variable (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (x : X) (hx : coheight x = 1)

/-- The finite sum of actual normal-branch orders with the actual residue-field degrees. -/
def normalizedBranchOrderSum (g : X.functionField) : ℤ := by
  let R := X.presheaf.stalk x
  let S := integralClosure R X.functionField
  let : IsDedekindDomain S := SupportNormalization.Constructions.stalk_normalization_isDedekind f x hx
  let : Module.Finite R S := SupportNormalization.Constructions.finite_stalk_normalization f x
  let : IsFractionRing S X.functionField :=
    integralClosure.isFractionRing_of_finite_extension X.functionField X.functionField
  let : Finite (HeightOneSpectrum S) := BranchOrder.Constructions.finite_heightOneSpectrum R S
  let := Fintype.ofFinite (HeightOneSpectrum S)
  exact ∑ P : HeightOneSpectrum S, (P.asIdeal.inertiaDeg R : ℤ) *
    SemilocalDivisorNorm.Constructions.localOrder P ((FractionRing.algEquiv S X.functionField).symm g)

theorem schemeOrd_eq_normalizedBranchOrderSum (g : X.functionField) (hg : g ≠ 0) :
    X.ord g x = normalizedBranchOrderSum X f x hx g := by
  let R := X.presheaf.stalk x
  let S := integralClosure R X.functionField
  let : IsDedekindDomain S := SupportNormalization.Constructions.stalk_normalization_isDedekind f x hx
  let : Module.Finite R S := SupportNormalization.Constructions.finite_stalk_normalization f x
  let : IsFractionRing S X.functionField :=
    integralClosure.isFractionRing_of_finite_extension X.functionField X.functionField
  let : Ring.KrullDimLE 1 R := krullDimLE_of_coheight_le hx.le
  let : Finite (HeightOneSpectrum S) := BranchOrder.Constructions.finite_heightOneSpectrum R S
  let := Fintype.ofFinite (HeightOneSpectrum S)
  rw [X.ord_eq_ordHom_of_coheight_eq_one hx]
  exact SemilocalDivisorNorm.Constructions.Normalization.log_ordFrac_eq_sum R S X.functionField g hg

end

end OAI.AlgebraicGeometry.CycleClass.Thom.NormalizedBranchOrder.Constructions.NormalizationLocal
