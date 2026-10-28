import OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.Cycles
import OAI.AlgebraicGeometry.FormalGeometry.Completion.CyclesTransport
import OAI.AlgebraicGeometry.FormalGeometry.Completion.RelativeCechZeroCycles
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechScalarCoface

/-! # Literal Cycles -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.LiteralCycles.Construction

noncomputable section

/-! Projective formal zero-cycles over the literal coefficient ring of Spec R. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.AlgebraicGeometry.Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
  (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation (Over.mk f)) [Flat f]

/-- The projective Cech complex over the original Spec R has actual formal zero-cycle
surjectivity, derived by transporting the constructed projective finite model. -/
theorem projectiveLiteralCech_formalZeroCycleComparisonSurjective (I : Ideal R) :
    Finite.FiniteModelCompletion.Construction.FormalZeroCycleComparisonSurjective I
      (RelativeCechZeroCycles.Construction.relativeStructureCechComplex f (Quotients.FiniteDescent.ProjectiveCechAt.Construction.ProjectiveCechComplex.cover (Over.mk f) P)) := by
  let S := Spec (CommRingCat.of R)
  let Z := Over.mk f
  have : Flat Z.hom := inferInstanceAs (Flat f)
  let U := Quotients.FiniteDescent.ProjectiveCechAt.Construction.ProjectiveCechComplex.cover Z P
  let b := Quotients.FiniteDescent.ProjectiveCechAt.Construction.ProjectiveCechComplex.base Z P
  let g := S.isoSpec.inv
  let ρ := (Scheme.ΓSpecIso (.of R)).inv.hom
  let J := I.map ρ
  have : IsNoetherianRing Γ(S, ⊤) :=
    isNoetherianRing_of_ringEquiv R (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm
  have hb : b ≫ g = f := by
    dsimp [b, Quotients.FiniteDescent.ProjectiveCechAt.Construction.ProjectiveCechComplex.base]
    rw [Quotients.FiniteDescent.ProjectivePresentation.Construction.ProjectivePresentationEmbedding.map_base, Category.assoc,
      Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]
    rfl
  have hraw := Cycles.Construction.projectiveCech_reducedKernelComparison_surjective Z P
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial X) (J.map g.appTop.hom)
  have hres := CyclesTransport.Construction.formalZeroCycleComparisonSurjective_restrictScalars g.appTop.hom J
    (Quotients.FiniteDescent.ProjectiveCechAt.Construction.ProjectiveCechComplex.complex Z P (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)) hraw
  have hnative : Finite.FiniteModelCompletion.Construction.FormalZeroCycleComparisonSurjective J
      (SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex f (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) U) := by
    rw [← hb]
    exact CyclesTransport.Construction.formalZeroCycleComparisonSurjective_of_iso J
      (Quotients.FiniteDescent.CechScalarCoface.Construction.CechScalarRestriction.complexIso b g (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) U).symm hres
  exact CyclesTransport.Construction.formalZeroCycleComparisonSurjective_restrictScalars ρ I
    (SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex f (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) U) hnative

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.LiteralCycles.Construction
