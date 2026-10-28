import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.Quotients
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointData

/-! # Point Data Specialization -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting

noncomputable section

/-! The original lifted and evaluated families specialize to the actual
native PEL data at their geometric moduli points, including integral action. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
variable {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
variable {iota : E →+* K} {κ : K →+* ℂ}
variable {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
variable {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
variable {D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q}
variable {R L : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field L] [Algebra R L] [IsFractionRing R L]
variable {b : B.R →+* R}
variable {residueIso : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R}

section

variable {x : D.GeometricPoint} (l : Lifts.IntegralLift D R b residueIso x)

theorem Lifts.IntegralLift.geometric_source_map :
    Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso) ≫ l.map =
      (D.geometricPointIntegralEquiv x).left := by
  change (Spec.map (CommRingCat.ofHom residueIso.symm.toRingHom) ≫ Lifts.closedBase R) ≫ l.map = _
  rw [Category.assoc, l.reduction]
  change Spec.map (CommRingCat.ofHom residueIso.symm.toRingHom) ≫
    (Spec.map (CommRingCat.ofHom residueIso.toRingHom) ≫ x.left ≫ D.specialProjection) = _
  have hρ : CommRingCat.ofHom residueIso.toRingHom ≫ CommRingCat.ofHom residueIso.symm.toRingHom =
      𝟙 (CommRingCat.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q)) := by
    apply CommRingCat.hom_ext
    exact RingHom.ext residueIso.symm_apply_apply
  rw [← Category.assoc, ← Spec.map_comp, hρ, Spec.map_id, Category.id_comp]
  rfl

/-- All PEL structures at the original point are retained by the
geometric reduction of the actual integral source. -/
def Lifts.IntegralLift.geometricActionIso : PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso
    (l.actionData.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso)))
    (D.pointDatum x).data := by
  have e := PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso.pullbackComp D.integral.universal.data l.map
    (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso))
  rw [l.geometric_source_map] at e
  exact e

end

variable (z : Evaluated.Targets.Lifts.EvaluatedTarget D R L b) (hbase : Lifts.ResidueCompatible D R b residueIso)

def Evaluated.Targets.Lifts.EvaluatedTarget.actionData := D.integral.universal.data.pullback z.extension

/-- The independent proper extension gives the complete datum at its
actual geometric reduction point. This comparison includes the action. -/
def Evaluated.Targets.Lifts.EvaluatedTarget.integralGeometricActionIso : PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso
    (z.actionData.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso)))
    (D.pointDatum (z.specialPoint hbase)).data := by
  have e := PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso.pullbackComp D.integral.universal.data z.extension
    (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso))
  have h : Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso) ≫ z.extension =
      (D.geometricPointIntegralEquiv (z.specialPoint hbase)).left :=
    (Category.assoc _ _ _).trans (z.specialPoint_projection hbase).symm
  rw [h] at e
  exact e

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting
