import OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.AffineCechAcyclic
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.Functor
import OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD

/-! # Truncated Cech -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.TruncatedCech.TruncatedCechAcyclic

noncomputable section

/-! The actual Čech terms of every native Hodge truncation retain coefficient Ext vanishing. -/

open _root_.CategoryTheory Abelian Limits ZeroObject _root_.AlgebraicGeometry Opposite

variable (R : Type) [CommRing R] [Algebra ℚ R]
  (X : Over (Spec (CommRingCat.of R))) [IsSeparated X.hom]
  {ι : Type} [Finite ι] (U : ι → X.left.Opens) (hU : ∀ i, IsAffineOpen (U i))

local instance : HasExt.{1} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) := HasExt.standard _

include hU in
theorem term_ext_subsingleton (r : ℤ) (j p q : ℕ) :
    Subsingleton (Ext.{1} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X)
      (((IntrinsicCech.Functor.IntrinsicCechFunctor.sheafFunctor R X.left U).obj
        ((AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) r).X j)).X p) (q + 1)) := by
  let G := IntrinsicCech.Functor.IntrinsicCechFunctor.sheafFunctor R X.left U ⋙
    HomologicalComplex.eval (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) (.up ℕ) p
  let H := (extFunctor.{1} (q + 1) : (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X)ᵒᵖ ⥤
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X ⥤ AddCommGrpCat.{1}).obj (op (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X))
  have : H.Additive := inferInstanceAs (extFunctorObj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X) (q + 1)).Additive
  change Subsingleton (H.obj (G.obj (if r ≤ (j : ℤ) then (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).X j else 0)))
  split_ifs with hj
  · exact GeometricComparison.Finite.AffineCechAcyclic.FiniteAffineCechAcyclic.sheafComplex_ext_subsingleton R X U hU j p q
  · exact AddCommGrpCat.subsingleton_of_isZero (H.map_isZero (G.map_isZero (isZero_zero _)))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.TruncatedCech.TruncatedCechAcyclic
