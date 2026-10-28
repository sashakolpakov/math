import OAI.AlgebraicGeometry.Crystalline.Cohomology.FlatBase.AffineOpenResolution
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.PushforwardExtVanishing
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Affine Open Pushforward Acyclic -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FlatBase.AffineOpenPushforwardAcyclic.FlatBaseAffineOpenPushforwardAcyclic

noncomputable section

/-! # Direct images of original form sheaves from affine opens are coefficient-Ext-acyclic -/

open _root_.CategoryTheory _root_.CategoryTheory.Abelian Limits _root_.AlgebraicGeometry Opposite

universe u

variable (R : Type u) [CommRing R] [Module.Flat ℤ R]
  (X : Over (Spec (CommRingCat.of R))) [IsProper X.hom] [Smooth X.hom]
  (U : X.left.Opens) (hU : IsAffineOpen U) (j : ℕ)

include hU in
theorem locallyExact
    (I : InjectiveResolution ((DeRhamGlobalId.DeRhamGlobal.sheafComplex R
      (AffineOpenResolution.FlatBaseAffineOpenResolution.openModel R X U)).X j)) :
    Cohomology.Module.PushforwardResolution.ModulePushforwardResolution.LocallyExact R U.inclusion' I := by
  let Y := AffineOpenResolution.FlatBaseAffineOpenResolution.openModel R X U
  let g : Y ⟶ X := AffineOpenResolution.FlatBaseAffineOpenResolution.inclusion R X U
  let : IsOpenImmersion g.left := inferInstanceAs (IsOpenImmersion U.ι)
  have : IsAffine U := hU
  have : IsAffineHom U.ι := IsAffineHom.of_comp U.ι X.hom
  intro V y
  obtain ⟨W, hW, hyW, hWV⟩ := exists_isAffineOpen_mem_and_subset y.property
  exact ⟨W, hWV, hyW, fun n => AffineOpenResolution.FlatBaseAffineOpenResolution.forms_sections_exact R
    X Y g j I (U.ι ⁻¹ᵁ W) (hW.preimage U.ι) n⟩

local instance coefficientExt : HasExt.{u + 1} (DeRhamGlobalId.DeRhamGlobal.Sheaves R X) := HasExt.standard _

include hU in
theorem ext_subsingleton (n : ℕ) :
    Subsingleton (Ext.{u + 1} (DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X)
      ((TopCat.Sheaf.pushforward (ModuleCat.{u} R) U.inclusion').obj
        ((DeRhamGlobalId.DeRhamGlobal.sheafComplex R (AffineOpenResolution.FlatBaseAffineOpenResolution.openModel R X U)).X j))
      (n + 1)) := by
  let Y := AffineOpenResolution.FlatBaseAffineOpenResolution.openModel R X U
  let g : Y ⟶ X := AffineOpenResolution.FlatBaseAffineOpenResolution.inclusion R X U
  let : IsOpenImmersion g.left := inferInstanceAs (IsOpenImmersion U.ι)
  let : IsAffine Y.left := hU
  let F := (DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y).X j
  let I : InjectiveResolution F := injectiveResolution F
  let : HasExt.{u + 1} (DeRhamGlobalId.DeRhamGlobal.Sheaves R Y) := HasExt.standard _
  let : Subsingleton (Ext.{u + 1} (ConstantSheaf.ConstantSheafSections.coefficient R (TopCat.of Y.left)) F (n + 1)) :=
    OrdinaryAffineVanishing.FlatBaseOrdinaryAffineVanishing.forms R X Y g j n
  exact Cohomology.Module.PushforwardExtVanishing.ModulePushforwardExtVanishing.ext_subsingleton R U.inclusion' I
    (locallyExact R X U hU j I) n
    (CoefficientResolution.CoefficientResolutionExactness.exactAt R (TopCat.of Y.left) I n)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FlatBase.AffineOpenPushforwardAcyclic.FlatBaseAffineOpenPushforwardAcyclic
