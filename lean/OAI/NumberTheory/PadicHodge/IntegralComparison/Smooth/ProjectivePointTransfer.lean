import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.CanonicalTransfer
import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ProjectiveSectionClassData

/-! # Projective Point Transfer -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ProjectivePointTransfer

noncomputable section

/-! The scalar-to-point quotient through the original projective
resolutions recovers its global class on the canonical complementary
cover. Purity and the refinement quasi-isomorphism follow from smooth
adjunction on the actual closed scheme. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.Survivor
  ProjectivePoint.GlobalTransferRecovery
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Module.Injective R R]
  [IsArtinianRing R] [IsLocalRing R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
variable (X : Over (Spec (CommRingCat.of R))) [Nonempty X.left]
  (i : X ⟶ Projective.IntrinsicOverlap.Intrinsic.model R (n+1)) [IsClosedImmersion i.left]
  [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
  (s₀ : Spec (CommRingCat.of R) ⟶ X.left) [IsClosedImmersion s₀]
  (hbase : s₀ ≫ X.hom = 𝟙 _) (B : ℕ) (hB : n+2 ≤ B)
  (g : ℕ) [SmoothOfRelativeDimension g X.hom]
local instance sourceSeparated : X.left.IsSeparated := by
  constructor
  rw [← terminal.comp_from X.hom]
  infer_instance
attribute [local instance] ProjectiveSectionClassData.composite_smooth
  ProjectiveFormTrace.composite_dimension
  ProjectiveFormTrace.composite_proper
  ProjectiveFormTrace.composite_connected
local notation "M" => OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.SectionClass.scalar i.left
local notation "hsec" => OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ProjectiveSectionClassData.section_over X i s₀ hbase
local notation "N" => OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g

include hB in
omit [Module.Injective R R] [IsArtinianRing R] [IsLocalRing R] [Nonempty ↥X.left] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] in
theorem exactAt (q : ℕ) (hq : q ≠ n+1-g) : (ProjectivePoint.GlobalTransferRecovery.coefficientDual B M).ExactAt q :=
  ProjectiveSerre.exactAt i.left B n (Fintype.card_fin (n+2)) hB g q hq

variable (U : (Proj (homogeneousSubmodule (Fin (n+2)) R)).Opens) (hU : IsAffineOpen U)
  {c : ℕ} (a : Fin c → Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U))
  (t : Fin g → Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U))
  (ha : Ideal.span (Set.range a) = i.left.ker.ideal ⟨U, hU⟩)
  (hat : KoszulPartial.Resolution.pointIdeal Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) a t =
    (s₀ ≫ i.left).ker.ideal ⟨U, hU⟩)

abbrev refinement_isIso := by
  letI := FormCoherence.Integral.quasicoherent R X g
  exact ProjectivePoint.CanonicalTransfer.refinement_isIso i.left s₀ B hB M (n+1-g)
    (exactAt X i B hB g) N (ProjectiveFormTrace.adjunctionIso X i B hB g)
    U hU a t ha hat

abbrev localize_recovery := by
  letI := FormCoherence.Integral.quasicoherent R X g
  exact ProjectivePoint.CanonicalTransfer.localize_recovery i.left s₀ hsec B hB M
    (Cech.StructurePullbackUnit.sheafMap s₀ i.left) (n+1-g) (exactAt X i B hB g)
    N (ProjectiveFormTrace.adjunctionIso X i B hB g) U hU a t ha hat

abbrev map_recovery := by
  letI := FormCoherence.Integral.quasicoherent R X g
  exact ProjectivePoint.CanonicalTransfer.map_recovery i.left s₀ hsec B hB M
    (Cech.StructurePullbackUnit.sheafMap s₀ i.left) (n+1-g) (exactAt X i B hB g)
    N (ProjectiveFormTrace.adjunctionIso X i B hB g) U hU a t ha hat

abbrev point_recovery := ConcreteCategory.congr_hom
  (map_recovery X i s₀ hbase B hB g U hU a t ha hat)
    (ProjectivePoint.SupportedClass.fixedPointClass i.left s₀ hsec B hB)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ProjectivePointTransfer
