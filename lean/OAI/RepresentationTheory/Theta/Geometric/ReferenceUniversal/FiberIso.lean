import OAI.RepresentationTheory.Theta.Geometric.Reference.ModuliPoints
import OAI.RepresentationTheory.Theta.Geometric.Universal.ModuliFaithfulness
import OAI.RepresentationTheory.Theta.Geometric.Universal.PELConditions
import OAI.RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm

/-! # Fiber Iso -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Equality with the original reference moduli point gives an actual
group isomorphism from its reference model to the native universal fiber. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    {D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA}
    {hg : D.pel.HasIntegralModelGeometry} {a : D.domain} (R : D.ReferencePELPointData hg a)
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsReduced S.left] (f : S ⟶ D.pel.complexSpace)
    (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) (hx : x ≫ f = R.point)

def Data.ActiveHeckeThetaData.ReferencePELPointData.universalFiberIso : AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso R.family ((Complex.PELClassification.complexUniversalFamily D.pel f).pullback x.left) := by
  have h : Nonempty (AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso (D.pel.model.family.pullback
      (Complex.PELClassification.modelComplexPointEquiv D.pel (x ≫ f)).left) R.family) := by
    rw [hx]
    exact R.point_family
  exact h.some.symm.trans (Universal.ModuliFaithfulness.complexUniversalFiber_modelIso D.pel f x)

def Data.ActiveHeckeThetaData.ReferencePELPointData.nativeUniversalFiberIso : R.model.abelian.toOver ≅
    (PolarizedCanonicalForm.polarizedFamilyPresentation (Universal.PELConditions.complexUniversalPolarized D.pel hg f) x).variety.toOver :=
  (R.universalFiberIso f x hx).abelian ≪≫
    (PolarizedCanonicalForm.polarizedFamilyPresentation (Universal.PELConditions.complexUniversalPolarized D.pel hg f) x).comparison

instance Data.ActiveHeckeThetaData.ReferencePELPointData.nativeUniversalFiberIso_group : IsMonHom (R.nativeUniversalFiberIso f x hx).hom := by
  let : IsMonHom (R.universalFiberIso f x hx).abelian.hom := (R.universalFiberIso f x hx).abelianGroup
  let : IsMonHom (PolarizedCanonicalForm.polarizedFamilyPresentation (Universal.PELConditions.complexUniversalPolarized D.pel hg f) x).comparison.hom :=
    (PolarizedCanonicalForm.polarizedFamilyPresentation (Universal.PELConditions.complexUniversalPolarized D.pel hg f) x).comparison_group
  change IsMonHom ((R.universalFiberIso f x hx).abelian.hom ≫
    (PolarizedCanonicalForm.polarizedFamilyPresentation (Universal.PELConditions.complexUniversalPolarized D.pel hg f) x).comparison.hom)
  infer_instance

end

end OAI.RepresentationTheory.Theta.Geometric
