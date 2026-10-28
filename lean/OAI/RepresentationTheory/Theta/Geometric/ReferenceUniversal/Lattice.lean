import OAI.RepresentationTheory.Theta.Geometric.ReferenceUniversal.RationalMarking
import OAI.RepresentationTheory.Theta.Geometric.Reference.PELEquiv

/-! # Lattice -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The actual reference-to-universal marking identifies exactly the
original full integral reference lattice. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local irreducible] Data.ActiveHeckeThetaData.ReferencePELPointData.universalFiberIso Data.ActiveHeckeThetaData.ReferencePELPointData.nativeUniversalFiberIso

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    {D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA}
    {hg : D.pel.HasIntegralModelGeometry} {a : D.domain} (R : D.ReferencePELPointData hg a)
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsReduced S.left] (f : S ⟶ D.pel.complexSpace)
    (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) (hx : x ≫ f = R.point)

theorem Data.ActiveHeckeThetaData.ReferencePELPointData.nativeUniversalRationalMarking_integral (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    R.nativeUniversalRationalMarking f x hx v ∈
      AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation (Universal.PELConditions.complexUniversalPolarized D.pel hg f) x).variety ↔
        v ∈ D.pel.reference.lattice := by
  let e := R.nativeUniversalFiberIso f x hx
  let M := R.model.toNativeReferenceModel R.analytic
  let : IsMonHom e.hom := R.nativeUniversalFiberIso_group f x hx
  change AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.hom (M.nativeReferenceMarking v) ∈ AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods _ ↔ _
  exact (Reference.PELEquiv.rationalLiftIso_integral_iff e (M.nativeReferenceMarking v)).trans
    (M.nativeReferenceMarking_integral v)

end

end OAI.RepresentationTheory.Theta.Geometric
