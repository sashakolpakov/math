import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.PolarizationOverlap
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.PolarizationPointTransport
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPrescribed.TransportCocycle
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralDual.Point

/-! # Polarization Relation -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The actual polarization maps the prescribed abelian descent
relation to the prescribed dual descent relation. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsReduced X.left] [IsLocallyNoetherian X.left]
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)
    (π : X ⟶ Q) [IsFinite π.left] [Etale π.left]
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPolarizationOverlap_target (hrigid : U.PrescribedRigid) :
    U.prescribedPolarizationOverlap π ≫ U.prescribedDualOverlapTarget hU π hk =
      U.prescribedOverlapTarget hU π hk ≫ U.prescribedPolarization := by
  let a := U.prescribedProjection
  let d := U.prescribedDualProjection
  let srcA := DescentCocycleChange.DescentCocycle.source π a
  let srcD := DescentCocycleChange.DescentCocycle.source π d
  let f := srcD ≫ d
  let g := DescentCocycleChange.DescentCocycle.base π d
  let f' := srcA ≫ a
  let g' := DescentCocycleChange.DescentCocycle.base π a
  let k := U.prescribedPolarizationOverlap π
  have h : f ≫ π = g ≫ π := DescentCocycleChange.DescentCocycle.source_condition π d
  have h' : f' ≫ π = g' ≫ π := DescentCocycleChange.DescentCocycle.source_condition π a
  have hf : k ≫ f = f' := by
    change k ≫ srcD ≫ d = srcA ≫ a
    rw [← Category.assoc, U.prescribedPolarizationOverlap_source, Category.assoc,
      U.prescribedPolarization_projection]
  have hg : k ≫ g = g' := U.prescribedPolarizationOverlap_base π
  have hn := U.prescribedDualPointTransport_natural hU π hk hrigid f g h srcD.left rfl k
  have hy : (srcA.left ≫ U.prescribedPolarization.left) ≫
      U.forgetAuxiliary.data.polarized.dual.abelian.scheme.hom = f'.left := by
    change (srcA.left ≫ U.prescribedPolarization.left) ≫ d.left = f'.left
    rw [Category.assoc, ← Over.comp_left, U.prescribedPolarization_projection]
    rfl
  have hpoints := U.prescribedDualPointTransport_congr hU π hk
    (k ≫ f) (k ≫ g) f' g'
    (by simpa only [Category.assoc] using congrArg (fun z => k ≫ z) h) h' hf hg
    (k.left ≫ srcD.left) (srcA.left ≫ U.prescribedPolarization.left) rfl hy
    (congrArg Over.Hom.left (U.prescribedPolarizationOverlap_source π))
  have hp := U.prescribedPointTransport_polarization hU π hk f' g' h' srcA.left rfl
  apply Over.OverMorphism.ext
  exact hn.symm.trans (hpoints.trans hp.symm)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
