import OAI.RepresentationTheory.Theta.Geometric.Reference.TateFrame
import OAI.RepresentationTheory.Theta.Geometric.Cleared.LocalRelativePosition

/-! # PEL Frame Lattices -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Original PEL reference frames have the standard source lattices;
the cleared actual isogenies have the exact prescribed relative positions. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    {D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA}
    {hg : D.pel.HasIntegralModelGeometry} {x : D.domain}
    (hgood : D.pel.IsGoodCompletelySplitPrime) (hdegree : Module.finrank ℚ E = 2 * s)
    (hc : D.HasFiniteCoordinates)

attribute [local irreducible] AlgebraicGeometry.AbelianScheme.TateComparison.RationalPeriod.rationalPeriodTateEquiv Data.ActiveHeckeThetaData.PeriodModel.referenceTateFrame

include hc in
theorem Data.ActiveHeckeThetaData.ReferencePELPointData.pelTateFrame_integral_image
    (R : D.ReferencePELPointData hg x) :
    AlgebraicGeometry.AbelianScheme.TateComparison.Rational.framedIntegralTateImage (R.pelTateFrame hgood hdegree) = D.jointLocalLattice :=
  R.model.referenceTateFrame_integral_image R.analytic hgood hdegree hc

include hg hgood hc in
theorem Data.ActiveHeckeThetaData.jointLocalLattice_eq_pi_standard :
    D.jointLocalLattice = Submodule.pi Set.univ (fun _ : Fin s × Bool => Data.ActiveHeckeThetaData.standardLocalLattice (q := q)) := by
  ext u
  exact (D.jointLocalLattice_standard hg hc hgood u).trans (by simp only [Submodule.mem_pi, Set.mem_univ, forall_true_left])

include hc in
theorem Data.ActiveHeckeThetaData.ReferencePELPointData.referenceTateFrame_sourceLattice
    (R : D.ReferencePELPointData hg x) (v : Fin s × Bool) :
    D.pel.framedSourceLattice (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) R.family
      (R.model.referenceTateFrame R.analytic hgood hdegree) v = Data.ActiveHeckeThetaData.standardLocalLattice (q := q) := by
  rw [AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.framedSourceLattice]
  rw [R.model.referenceTateFrame_integral_image R.analytic hgood hdegree hc,
    Data.ActiveHeckeThetaData.jointLocalLattice_eq_pi_standard (hg := hg) hgood hc]
  exact AlgebraicGeometry.AbelianScheme.TateComparison.FramedSourceDecomposition.submodule_pi_map_proj (fun _ : Fin s × Bool => Data.ActiveHeckeThetaData.standardLocalLattice (q := q)) v

end

end OAI.RepresentationTheory.Theta.Geometric
