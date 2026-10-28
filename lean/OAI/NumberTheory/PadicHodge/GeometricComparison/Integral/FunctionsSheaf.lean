import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.LowDegreeSheaves

/-! # Functions Sheaf -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.FunctionsSheaf.IntegralFunctionsSheaf

noncomputable section

/-! The native integral zero-form sheaf is the actual structure sheaf with its base-ring module action. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (R : Type u) [CommRing R] (X : Over (Spec (.of R)))

theorem isSheaf : Presheaf.IsSheaf (Opens.grothendieckTopology X.left)
    (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.functionsPresheaf R X) := by
  apply (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{u} R))).mpr
  change Presheaf.IsSheaf (Opens.grothendieckTopology X.left)
    (X.left.presheaf ⋙ forget CommRingCat.{u})
  exact (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget CommRingCat.{u})).mp X.left.IsSheaf

def sheaf : Sheaf (Opens.grothendieckTopology X.left) (ModuleCat.{u} R) :=
  ⟨AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.functionsPresheaf R X, isSheaf R X⟩

def zeroTermIso : (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).X 0 ≅ sheaf R X :=
  LowDegreeSheaves.IntegralLowDegreeSheaves.zeroSheafIso R X ≪≫
    (sheafificationIso (sheaf R X)).symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.FunctionsSheaf.IntegralFunctionsSheaf
