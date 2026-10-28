import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OpenResolution
import OAI.NumberTheory.PadicHodge.GeometricComparison.Module.PushforwardExtVanishing
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Open Pushforward Acyclic -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OpenPushforwardAcyclic.AffineOpenPushforwardAcyclic

noncomputable section

/-! Direct images of native form sheaves from affine opens of separated rational schemes are acyclic. -/

open _root_.CategoryTheory Abelian Limits _root_.AlgebraicGeometry Opposite

variable (R : Type) [CommRing R] [Algebra ℚ R]
  (X : Over (Spec (CommRingCat.of R))) [IsSeparated X.hom]
  (U : X.left.Opens) (hU : IsAffineOpen U) (j : ℕ)

include hU in
theorem locallyExact
    (I : InjectiveResolution ((OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R (OpenResolution.AffineOpenResolution.openModel R X U)).X j)) :
    Module.PushforwardResolution.ModulePushforwardResolution.LocallyExact R U.inclusion' I := by
  have : IsAffine U := hU
  have : IsAffineHom U.ι := IsAffineHom.of_comp U.ι X.hom
  intro V y
  obtain ⟨W, hW, hyW, hWV⟩ := exists_isAffineOpen_mem_and_subset y.property
  exact ⟨W, hWV, hyW, fun n => OpenResolution.AffineOpenResolution.forms_sections_exact R
    (OpenResolution.AffineOpenResolution.openModel R X U) j I (U.ι ⁻¹ᵁ W) (hW.preimage U.ι) n⟩

local instance : HasExt.{1} (OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) := HasExt.standard _

include hU in
theorem ext_subsingleton (n : ℕ) :
    Subsingleton (Ext.{1} (OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X)
      ((TopCat.Sheaf.pushforward (ModuleCat R) U.inclusion').obj
        ((OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R (OpenResolution.AffineOpenResolution.openModel R X U)).X j)) (n + 1)) := by
  let Y := OpenResolution.AffineOpenResolution.openModel R X U
  have : IsAffine Y.left := hU
  let : Algebra ℚ Γ(Y.left, ⊤) := Rational.AffineFormVanishing.RationalAffineFormVanishing.sectionAlgebra R Y ⊤
  let F := (OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y).X j
  let I : InjectiveResolution F := injectiveResolution F
  exact Module.PushforwardExtVanishing.ModulePushforwardExtVanishing.ext_subsingleton R U.inclusion' I
    (locallyExact R X U hU j I) n
    (ChartExtVanishing.AffineChartExtVanishing.evaluated_exactAt R Y F (CechAcyclic.AffineCechAcyclic.forms R Y j) I n)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OpenPushforwardAcyclic.AffineOpenPushforwardAcyclic
