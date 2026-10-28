import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OrdinaryFraction

/-! # Ordinary Fraction Scalar -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OrdinaryFractionScalar.Ordinary

noncomputable section

/-! Moving a section scalar into the numerator of the original
ordinary principal fraction, with its kernel-normalized consequence. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf
variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
  (N : X.Modules) (ω : Γ(N,U)) {m : ℕ} (t : Fin m → Γ(X,U))

theorem value_smul (z a : Γ(X,U)) :
    OrdinaryFraction.Ordinary.value U hU N (z • ω) t a = OrdinaryFraction.Ordinary.value U hU N ω t (z*a) := by
  unfold OrdinaryFraction.Ordinary.value
  congr 1
  let r : SectionPresheaf.Index U :=
    AugmentedOrdered.CechCoordinates.topObject (PrincipalPoint.Fraction.family U t) m (by simp)
  change (OrdinaryFraction.Ordinary.reciprocal U hU t * algebraMap Γ(X,U) Γ(X,SectionPresheaf.openSubset U r) a) •
      N.presheaf.map (SectionPresheaf.inclusion U r).op (z • ω) =
    (OrdinaryFraction.Ordinary.reciprocal U hU t * algebraMap Γ(X,U) Γ(X,SectionPresheaf.openSubset U r) (z*a)) •
      N.presheaf.map (SectionPresheaf.inclusion U r).op ω
  rw [N.map_smul, ← mul_smul, map_mul]
  congr 1
  change (OrdinaryFraction.Ordinary.reciprocal U hU t * algebraMap Γ(X,U) _ a) *
      algebraMap Γ(X,U) _ z =
    OrdinaryFraction.Ordinary.reciprocal U hU t * (algebraMap Γ(X,U) _ z * algebraMap Γ(X,U) _ a)
  exact (mul_assoc _ _ _).trans (congrArg (OrdinaryFraction.Ordinary.reciprocal U hU t * ·) (mul_comm _ _))

theorem section_weighted_of_kernel {k : Type u} [CommRing k] (η : Γ(X,U) →+* k)
    (hk : Koszul.OrientedTopCohomology.ideal Γ(X,U) t = RingHom.ker η)
    (z : Γ(X,U)) (hz : η z = 1) (a : Γ(X,U)) :
    OrdinaryFraction.Ordinary.value U hU N (z • ω) t a = OrdinaryFraction.Ordinary.value U hU N ω t a :=
  (value_smul U hU N ω t z a).trans (OrdinaryFraction.Ordinary.weighted_of_kernel U hU N ω t η hk z hz a)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OrdinaryFractionScalar.Ordinary
