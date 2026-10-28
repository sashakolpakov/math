import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.AwayRationalEquiv
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.FiniteAway

/-! # Unitary Away Topology -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.UnitaryAwayTopology

noncomputable section

/-! The actual native residual range also carries the topology of the
CM unitary local factors away from a specified finite place. The map is
constructed through the faithful rational-source equivalence. -/

open scoped Classical _root_.Matrix _root_.NumberField

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.FiniteAway.Approximation

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
  (w : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace (NumberField.maximalRealSubfield E))

def nativeUnitaryAwayHom : RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.NativeAway E D hg hμ v hv e he c u hu →*
    CM.FiniteAway.Approximation.CMFiniteAway E D.pel.reference hg.reference_admissible w :=
  (CM.FiniteAway.Approximation.cmRationalFiniteAway E D.pel.reference hg.reference_admissible w).comp
    (AwayRationalEquiv.nativeAwayRationalEquiv E D hg hμ v hv e he c u hu).symm.toMonoidHom

theorem nativeUnitaryAwayHom_rational (g : D.RationalSU) :
    nativeUnitaryAwayHom E D hg hμ v hv e he c u hu w
        (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeAway E D hg hμ v hv e he c u hu g) =
      CM.FiniteAway.Approximation.cmRationalFiniteAway E D.pel.reference hg.reference_admissible w g := by
  exact congrArg (CM.FiniteAway.Approximation.cmRationalFiniteAway E D.pel.reference hg.reference_admissible w)
    (AwayRationalEquiv.nativeAwayRationalEquiv_symm_apply E D hg hμ v hv e he c u hu g)

@[instance_reducible]
def nativeUnitaryAwayTopology : TopologicalSpace (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.NativeAway E D hg hμ v hv e he c u hu) :=
  TopologicalSpace.induced (nativeUnitaryAwayHom E D hg hμ v hv e he c u hu w) inferInstance

theorem nativeUnitaryAway_topologicalGroup :
    @IsTopologicalGroup (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.NativeAway E D hg hμ v hv e he c u hu)
      (nativeUnitaryAwayTopology E D hg hμ v hv e he c u hu w) _ := by
  let : IsTopologicalGroup (CM.FiniteAway.Approximation.CMFiniteAway E D.pel.reference hg.reference_admissible w) :=
    CM.FiniteAway.Approximation.cmFiniteAway_topologicalGroup E D.pel.reference hg.reference_admissible w
  exact isTopologicalGroup_induced (nativeUnitaryAwayHom E D hg hμ v hv e he c u hu w)

theorem nativeUnitaryAway_continuous :
    letI := nativeUnitaryAwayTopology E D hg hμ v hv e he c u hu w
    Continuous (nativeUnitaryAwayHom E D hg hμ v hv e he c u hu w) :=
  continuous_induced_dom

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.UnitaryAwayTopology
