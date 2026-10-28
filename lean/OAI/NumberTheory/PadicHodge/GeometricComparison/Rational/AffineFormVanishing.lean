import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.ChartExtVanishing

/-! # Affine Form Vanishing -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Rational.AffineFormVanishing.RationalAffineFormVanishing

noncomputable section

/-! Over a rational base, the affine vanishing theorem applies to the actual native section algebras without further coefficient assumptions. -/

open _root_.CategoryTheory Abelian _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] [Algebra ℚ R] (X : Over (Spec (CommRingCat.of R)))

@[instance_reducible] def sectionAlgebra (U : X.left.Opens) : Algebra ℚ Γ(X.left, U) :=
  ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionBaseMap R X U).comp (algebraMap ℚ R)).toAlgebra

local instance : HasExt.{1} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) := HasExt.standard _

theorem forms_ext_subsingleton [IsAffine X.left] (j n : ℕ) :
    Subsingleton (Ext.{1} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X)
      ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).X j) (n + 1)) := by
  let : Algebra ℚ Γ(X.left, ⊤) := sectionAlgebra R X ⊤
  exact Affine.ChartExtVanishing.AffineChartExtVanishing.forms_ext_subsingleton R X j n

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Rational.AffineFormVanishing.RationalAffineFormVanishing
