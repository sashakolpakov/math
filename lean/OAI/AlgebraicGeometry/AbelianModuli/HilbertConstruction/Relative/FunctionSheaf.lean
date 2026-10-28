import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.AffineLineFunctions
import Mathlib.CategoryTheory.Sites.SubcanonicalOver

/-! # Function Sheaf -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.FunctionSheaf

noncomputable section

/-! Regular functions satisfy descent for the relative fppf and fpqc topologies. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem relativeFunctionPresheaf_isSheaf_fppf (S : Scheme.{u}) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (AffineLineFunctions.relativeFunctionPresheaf S) :=
  (Presheaf.isSheaf_of_iso_iff (J := Scheme.fppfTopology.over S) (AffineLineFunctions.relativeFunctionPresheafIso S)).mp
    ((isSheaf_iff_isSheaf_of_type _ _).mpr
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _))

theorem relativeFunctionPresheaf_isSheaf_fpqc (S : Scheme.{u}) :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over S) (AffineLineFunctions.relativeFunctionPresheaf S) :=
  (Presheaf.isSheaf_of_iso_iff (J := Scheme.fpqcTopology.over S) (AffineLineFunctions.relativeFunctionPresheafIso S)).mp
    ((isSheaf_iff_isSheaf_of_type _ _).mpr
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.FunctionSheaf
