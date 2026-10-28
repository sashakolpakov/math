import OAI.RepresentationTheory.Hecke.IntrinsicDatum
import Mathlib.Topology.Algebra.Group.Matrix

/-! # Away Topology -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.AwayTopology

noncomputable section

/-! The native away range inherits its topology from its actual finite
adelic symplectic matrices. Both the matrix and its inverse are retained
by the canonical map to matrix units. -/

open scoped Classical _root_.Matrix
open OAI.RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic

attribute [local instance] Multiplicity.nativePlaceDecidableEq Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
  [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
  (hg : D.pel.HasIntegralModelGeometry) (hμ : D.pel.reference.μ = E.val.toRingHom)
  (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
  (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
    Algebra.trace ℚ E (D.pel.reference.imaginaryScalar * Multiplicity.nativeTensorPairing E D.pel.reference v x y))
  {n : ℕ} (c : (Fin s × Fin 3) ≃ Fin n) (u : MpF)
  (hu : FiniteDilation.NativeFiniteCoordinateIdentity E D e u)

def nativeAwayMatrixHom : RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.NativeAway E D hg hμ v hv e he c u hu →*
    (Matrix (Sum (Fin s × Fin 3) (Fin s × Fin 3))
      (Sum (Fin s × Fin 3) (Fin s × Fin 3)) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ :=
  ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin s × Fin 3) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf).subtype.toHomUnits).comp
    (D.weil.finite.project.comp (RepresentationTheory.Hecke.BlockResidual.SphericalActionIntrinsic.activeResidual E D hg hμ v hv e he c u hu).range.subtype)

@[instance_reducible]
def nativeAwayTopology : TopologicalSpace (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.NativeAway E D hg hμ v hv e he c u hu) :=
  TopologicalSpace.induced (nativeAwayMatrixHom E D hg hμ v hv e he c u hu) inferInstance

theorem nativeAway_topologicalGroup :
    @IsTopologicalGroup (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.NativeAway E D hg hμ v hv e he c u hu)
      (nativeAwayTopology E D hg hμ v hv e he c u hu) _ :=
  isTopologicalGroup_induced (nativeAwayMatrixHom E D hg hμ v hv e he c u hu)

theorem nativeAway_matrix_continuous :
    letI := nativeAwayTopology E D hg hμ v hv e he c u hu
    Continuous (fun a : RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.NativeAway E D hg hμ v hv e he c u hu => (D.weil.finite.project a.val).val) := by
  let := nativeAwayTopology E D hg hμ v hv e he c u hu
  exact Units.continuous_val.comp (show Continuous (nativeAwayMatrixHom E D hg hμ v hv e he c u hu)
    from continuous_induced_dom)

theorem nativeAway_inverse_matrix_continuous :
    letI := nativeAwayTopology E D hg hμ v hv e he c u hu
    Continuous (fun a : RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.NativeAway E D hg hμ v hv e he c u hu => (D.weil.finite.project a.val⁻¹).val) := by
  let := nativeAwayTopology E D hg hμ v hv e he c u hu
  have hc := Units.continuous_coe_inv.comp
    (show Continuous (nativeAwayMatrixHom E D hg hμ v hv e he c u hu) from continuous_induced_dom)
  change Continuous (fun a : RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.NativeAway E D hg hμ v hv e he c u hu =>
    ((D.weil.finite.project a.val)⁻¹).val) at hc
  exact hc.congr (fun a => congrArg Subtype.val (D.weil.finite.project.map_inv a.val).symm)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.AwayTopology
