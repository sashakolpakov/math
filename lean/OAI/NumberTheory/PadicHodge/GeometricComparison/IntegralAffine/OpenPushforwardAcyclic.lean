import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralAffine.OpenResolution
import OAI.NumberTheory.PadicHodge.GeometricComparison.Module.PushforwardExtVanishing
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Open Pushforward Acyclic -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralAffine.OpenPushforwardAcyclic.IntegralAffineOpenPushforwardAcyclic

noncomputable section

/-! Direct images of native form sheaves from affine opens of separated integral schemes are acyclic. -/

open _root_.CategoryTheory Abelian Limits _root_.AlgebraicGeometry Opposite

variable (R : Type) [CommRing R] [Module.Flat ℤ R]
  (X : Over (Spec (CommRingCat.of R))) [IsSeparated X.hom]
  (U : X.left.Opens) (hU : IsAffineOpen U) (j : ℕ) (hj : j ≤ 2)

include hU hj in
theorem locallyExact
    (I : InjectiveResolution ((OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R (OpenResolution.IntegralAffineOpenResolution.openModel R X U)).X j)) :
    GeometricComparison.Module.PushforwardResolution.ModulePushforwardResolution.LocallyExact R U.inclusion' I := by
  have : IsAffine U := hU
  have : IsAffineHom U.ι := IsAffineHom.of_comp U.ι X.hom
  intro V y
  obtain ⟨W, hW, hyW, hWV⟩ := exists_isAffineOpen_mem_and_subset y.property
  exact ⟨W, hWV, hyW, fun n => OpenResolution.IntegralAffineOpenResolution.forms_sections_exact R
    (OpenResolution.IntegralAffineOpenResolution.openModel R X U) j hj I (U.ι ⁻¹ᵁ W) (hW.preimage U.ι) n⟩

local instance : HasExt.{1} (OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) := HasExt.standard _

include hU hj in
theorem ext_subsingleton (n : ℕ) :
    Subsingleton (Ext.{1} (OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X)
      ((TopCat.Sheaf.pushforward (ModuleCat R) U.inclusion').obj
        ((OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R (OpenResolution.IntegralAffineOpenResolution.openModel R X U)).X j)) (n + 1)) := by
  let Y := OpenResolution.IntegralAffineOpenResolution.openModel R X U
  have : IsAffine Y.left := hU
  let F := (OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y).X j
  let I : InjectiveResolution F := injectiveResolution F
  exact GeometricComparison.Module.PushforwardExtVanishing.ModulePushforwardExtVanishing.ext_subsingleton R U.inclusion' I
    (locallyExact R X U hU j hj I) n
    (OpenResolution.IntegralAffineOpenResolution.forms_exactAt R Y j hj I ⊤ (isAffineOpen_top Y.left) n)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralAffine.OpenPushforwardAcyclic.IntegralAffineOpenPushforwardAcyclic
