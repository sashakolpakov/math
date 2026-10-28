import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.RefinementTotalCup
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.CoverRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.CoverRefinementQuasiIso
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCechUnit
import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.AffineOpenFormsUnit
import OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexMap

/-! # Cover Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RationalDeRham.CoverRefinement

noncomputable section

/-! The actual full ordinary de Rham Čech refinement on rational
coefficients is a quasi-isomorphism between affine covers. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R : Type) [CommRing R] [Algebra ℚ R]
  (X : Over (Spec (CommRingCat.of R))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  {ι κ : Type} (U : ι → X.left.Opens) (V : κ → X.left.Opens)
  (r : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)
  (hU : iSup U = ⊤) (hV : iSup V = ⊤)
  (haU : ∀ i, IsAffineOpen (U i)) (haV : ∀ i, IsAffineOpen (V i))

def unitRow {τ : Type} (W : τ → X.left.Opens) (q : ℕ) :=
  (NonemptyCechNerve.complexFunctor W).map ((AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCechUnit.BaseSmallDeRhamCechUnit.unit R X).f q)

omit [IsProper X.hom] [Smooth X.hom] in
theorem unitRow_isIso {τ : Type} (W : τ → X.left.Opens)
    (haW : ∀ i, IsAffineOpen (W i)) (q : ℕ) : IsIso (unitRow R X W q) :=
  GeometricComparison.Cech.TermwiseIso.CechTermwiseIso.isIso (NonemptyCechNerve.nerve W) ((AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCechUnit.BaseSmallDeRhamCechUnit.unit R X).f q)
    (fun n t => GeometricComparison.Intrinsic.AffineOpenFormsUnit.IntrinsicAffineOpenFormsUnit.on_open R X (∏ᶜ (W ∘ t))
      (AlgebraicGeometry.SheafCohomology.Cech.Cochains.IsAffineOpen.cechIntersection W haW n t) q)

include hU hV haU haV in
omit [Algebra ℚ R] in
theorem native_row_quasiIso (q : ℕ) : QuasiIso
    (GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.map U V r ((IntrinsicDeRham.CechComplex.Intrinsic.presheafComplex R X).X q)) := by
  let : (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X q).IsQuasicoherent :=
    IntegralComparison.Smooth.FormCoherence.Integral.quasicoherent R X q
  let : QuasiIso (ModuleCech.CoverRefinement.map R X U V r
      (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X q)) :=
    ModuleCech.CoverRefinementQuasiIso.quasiIso R X U V r (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X q)
      hU hV haU haV
  change QuasiIso ((IntrinsicDeRham.CoverRefinement.Intrinsic.bicomplexMap R X U V r).f q)
  apply (quasiIso_iff_comp_left (IntrinsicDeRham.TopEdge.Intrinsic.rowIso R X U q).hom _).mp
  rw [IntrinsicDeRham.CoverRefinement.Intrinsic.rowIso_natural]
  infer_instance

include hU hV haU haV in
theorem row_quasiIso (q : ℕ) : QuasiIso
    (GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.map U V r ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X).X q)) := by
  let : IsIso (unitRow R X U q) := unitRow_isIso R X U haU q
  let : IsIso (unitRow R X V q) := unitRow_isIso R X V haV q
  let := native_row_quasiIso R X U V r hU hV haU haV q
  apply (quasiIso_iff_comp_right _ (unitRow R X V q)).mp
  change QuasiIso (GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.map U V r ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X).X q) ≫
    (NonemptyCechNerve.complexFunctor V).map ((AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCechUnit.BaseSmallDeRhamCechUnit.unit R X).f q))
  rw [← GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.naturality]
  exact quasiIso_comp _ _ (hφ := quasiIso_of_isIso (unitRow R X U q))
    (hφ' := native_row_quasiIso R X U V r hU hV haU haV q)

include hU hV haU haV in
theorem quasiIso : QuasiIso
    (Cech.RefinementTotalCup.map U V r (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)) :=
  AlgebraicTopology.DeRham.Comparison.DoubleComplexMap.DoubleComplex.total_map_quasiIso_of_columns
    (Cech.RefinementTotalCup.bicomplexMap U V r (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X))
    (fun q => row_quasiIso R X U V r hU hV haU haV q)

def homologyIso (q : ℕ) := by
  letI := quasiIso R X U V r hU hV haU haV
  exact isoOfQuasiIsoAt
    (Cech.RefinementTotalCup.map U V r (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)) q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RationalDeRham.CoverRefinement
