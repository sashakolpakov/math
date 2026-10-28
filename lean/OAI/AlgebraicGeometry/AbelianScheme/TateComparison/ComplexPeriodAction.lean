import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FiberProjectivity
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PELMarking

/-! # Complex Period Action -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The actual PEL action on a complex fiber gives a rank-three
number-field marking of its periods and a full stable integral lattice. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PELMarking.IntrinsicPELMarking

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (h : D.HasIntegralModelGeometry)
  (b : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ Spec (.of K)) (x : D.GeometricPoint b)

def Data.SphericalPELAlbaneseData.complexFiberNative : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety :=
  AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native (D.fiberFamily b x).abelian (D.complexFiberProjectivePresentation h b x)

abbrev Data.SphericalPELAlbaneseData.complexFiberPeriods := AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (D.complexFiberNative h b x)

def Data.SphericalPELAlbaneseData.complexFiberPeriodFieldAction : E →ₐ[ℚ] Module.End ℚ (D.complexFiberPeriods h b x) :=
  AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldAction (D.fiberFamily b x).abelian (D.complexFiberProjectivePresentation h b x)
    (PELAdapters.actionFromEnd (D.fiberFamily b x).action)

abbrev Data.SphericalPELAlbaneseData.complexFiberPeriodModule : Module E (D.complexFiberPeriods h b x) :=
  Module.compHom (D.complexFiberPeriods h b x) (D.complexFiberPeriodFieldAction h b x).toRingHom

theorem Data.SphericalPELAlbaneseData.complexFiberPeriod_finrank (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s) :
    let := D.complexFiberPeriodModule h b x
    Module.finrank E (D.complexFiberPeriods h b x) = 3 :=
  AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.field_finrank_three (D.fiberFamily b x).abelian (D.complexFiberProjectivePresentation h b x)
    (PELAdapters.actionFromEnd (D.fiberFamily b x).action) s hs rfl hdegree

def Data.SphericalPELAlbaneseData.complexFiberPeriodCoordinates (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s) :
    let := D.complexFiberPeriodModule h b x
    D.complexFiberPeriods h b x ≃ₗ[E] (Fin 3 → E) :=
  AbelianModuli.ReferenceFamily.Intrinsic.PELMarking.IntrinsicPELMarking.coordinates (D.fiberFamily b x).abelian (D.complexFiberProjectivePresentation h b x)
    (PELAdapters.actionFromEnd (D.fiberFamily b x).action) s hs rfl hdegree

def Data.SphericalPELAlbaneseData.complexFiberMarkedPeriodLattice (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s) :
    Submodule ℤ (Fin 3 → E) :=
  AbelianModuli.ReferenceFamily.Intrinsic.PELMarking.IntrinsicPELMarking.markedLattice (D.fiberFamily b x).abelian (D.complexFiberProjectivePresentation h b x)
    (PELAdapters.actionFromEnd (D.fiberFamily b x).action) s hs rfl hdegree

theorem Data.SphericalPELAlbaneseData.complexFiberMarkedPeriodLattice_full_stable (hs : 0 < s)
    (hdegree : Module.finrank ℚ E = 2 * s) :
    NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice (D.complexFiberMarkedPeriodLattice h b x hs hdegree) :=
  AbelianModuli.ReferenceFamily.Intrinsic.PELMarking.IntrinsicPELMarking.markedLattice_full_stable (D.fiberFamily b x).abelian (D.complexFiberProjectivePresentation h b x)
    (PELAdapters.actionFromEnd (D.fiberFamily b x).action) s hs rfl hdegree

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
