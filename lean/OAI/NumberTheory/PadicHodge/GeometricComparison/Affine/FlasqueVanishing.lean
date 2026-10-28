import OAI.NumberTheory.PadicHodge.GeometricComparison.Rational.AffineFormVanishing

/-! # Flasque Vanishing -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.FlasqueVanishing.AffineFlasqueVanishing

noncomputable section

/-! Positive coefficient Ext of flasque module sheaves vanishes on rational affine schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  (F : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) [TopCat.Sheaf.IsFlasque F]

theorem cech_acyclic : CechAcyclic.AffineCechAcyclic.Acyclic R X F := by
  intro A _ _ _ f _ t ht n
  have : TopCat.Sheaf.IsFlasque ((AlgebraicGeometry.Crystalline.Cohomology.Cech.Cover.CechRestriction.sheafRestrictionFunctor R f.left).obj F) :=
    Module.InjectiveFlasque.ModuleInjectiveFlasque.restriction R F f.left
  apply Module.FlasqueCech.ModuleFlasqueCech.exactAt_succ R (RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R A)
    ((AlgebraicGeometry.Crystalline.Cohomology.Cech.Cover.CechRestriction.sheafRestrictionFunctor R f.left).obj F)
    (fun a : t => PrimeSpectrum.basicOpen a.val) _ n
  apply PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr
  simpa only [Subtype.range_coe_subtype, Finset.setOfPred_mem] using ht

local instance : HasExt.{1} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) := HasExt.standard _

theorem ext_subsingleton [Algebra ℚ R] [IsAffine X.left] (n : ℕ) :
    Subsingleton (Abelian.Ext.{1} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X) F (n + 1)) := by
  let : Algebra ℚ Γ(X.left, ⊤) := Rational.AffineFormVanishing.RationalAffineFormVanishing.sectionAlgebra R X ⊤
  exact ChartExtVanishing.AffineChartExtVanishing.ext_subsingleton R X F (cech_acyclic R X F) n

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.FlasqueVanishing.AffineFlasqueVanishing
