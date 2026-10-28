import OAI.AlgebraicGeometry.SheafCohomology.Projective.OverScalarRestriction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.Nonvanishing

/-! # Over Section -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.OverSection

noncomputable section

/-! The nonvanishing open of a section from its coordinate on an over-site. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.Nonvanishing
open OAI.AlgebraicGeometry.SheafCohomology.Projective.OverScalarRestriction

universe u

namespace Construction.OverSectionLocus

variable {X : Scheme.{u}} {M : X.Modules}

theorem coordinate_eq (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M) (U : X.Opens)
    (e : M.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (r : Γ(X, U))
    (h : e.hom.val.app (.op (Over.mk (𝟙 U))) (s.app U (1 : Γ(X, U))) = r) :
    s.over U ≫ e.hom =
      SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U r := by
  apply _root_.SheafOfModules.hom_ext
  ext V
  have hn := PresheafOfModules.naturality_apply (s.over U ≫ e.hom).val
    (Over.homMk V.unop.hom : V.unop ⟶ Over.mk (𝟙 U)).op (1 : Γ(X, U))
  change e.hom.val.app V (s.app V.unop.left (X.presheaf.map V.unop.hom.op 1)) =
    X.presheaf.map V.unop.hom.op
      (e.hom.val.app (.op (Over.mk (𝟙 U))) (s.app U (1 : Γ(X, U)))) at hn
  rw [map_one, h] at hn
  change e.hom.val.app V (s.app V.unop.left (1 : Γ(X, V.unop.left))) =
    1 * X.presheaf.map V.unop.hom.op r
  simpa only [one_mul] using hn

theorem isIso_over_iff (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M) (U : X.Opens) :
    IsIso (s.over U) ↔ IsIso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection U.ι s) := by
  rw [AbelianModuli.HilbertConstruction.Section.Nonvanishing.isIso_pullbackSection_iff]
  let F := (Scheme.Modules.overEquiv U).functor
  let e := Scheme.Modules.overFunctorEquiv U ≪≫ Scheme.Modules.restrictFunctorIsoPullback U.ι
  rw [← isIso_iff_of_reflects_iso (s.over U) F]
  have h : F.map (s.over U) ≫ (e.app M).hom =
      (e.app (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)).hom ≫ (Scheme.Modules.pullback U.ι).map s :=
    e.hom.naturality s
  exact (isIso_comp_right_iff _ (e.app M).hom).symm.trans
    ((congrArg IsIso h).to_iff.trans (isIso_comp_left_iff (e.app (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)).hom _))

local instance (Y : Scheme.{u}) :
    ∀ V, IsMulCommutative (Y.ringCatSheaf.obj.obj V) := fun V => by
  change IsMulCommutative (Y.presheaf.obj V)
  exact IsMulCommutative.of_comm fun a b => mul_comm a b

theorem scalar_isIso_iff (U : X.Opens) (r : Γ(X, U)) :
    IsIso (SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U r) ↔
      IsUnit r := by
  rw [← isUnit_iff_isIso]
  exact MulEquiv.isUnit_map (f :=
    (SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEndRingEquiv
      X.ringCatSheaf U).toMulEquiv)

theorem restrict_coordinate (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M) (U : X.Opens)
    (e : M.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (r : Γ(X, U))
    (h : s.over U ≫ e.hom =
      SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U r)
    {V : X.Opens} (hV : V ≤ U) :
    s.over V ≫
      (SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization
        X.ringCatSheaf M U e (Over.mk (homOfLE hV))).hom =
      SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf V
        (X.presheaf.map (homOfLE hV).op r) := by
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change Γ(X, W.unop.left) at a
  have hh := congrArg (fun q => q.val.app (.op ((Over.map (homOfLE hV)).obj W.unop))) h
  have ha := ConcreteCategory.congr_hom hh
    (show ((AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X).over U).val.obj
      (.op ((Over.map (homOfLE hV)).obj W.unop)) from a)
  change e.hom.val.app (.op ((Over.map (homOfLE hV)).obj W.unop))
      (s.app W.unop.left a) =
    a * X.presheaf.map W.unop.hom.op (X.presheaf.map (homOfLE hV).op r)
  rw [← X.presheaf.map_comp_apply]
  exact ha

theorem nonvanishing (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M) (U : X.Opens)
    (e : M.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (r : Γ(X, U))
    (h : s.over U ≫ e.hom =
      SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U r) :
    AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s ⊓ U = X.basicOpen r := by
  have hiso {V : X.Opens} (hV : V ≤ U) :
      IsIso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection V.ι s) ↔ IsUnit (X.presheaf.map (homOfLE hV).op r) := by
    rw [← isIso_over_iff]
    let eV := SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization
      X.ringCatSheaf M U e (Over.mk (homOfLE hV))
    rw [← isIso_comp_right_iff (s.over V) eV.hom, restrict_coordinate s U e r h hV]
    exact scalar_isIso_iff V _
  apply le_antisymm
  · intro x hx
    obtain ⟨V, hV, hxV⟩ := Opens.mem_sSup.mp hx.1
    change X.Opens at V
    have : IsIso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection V.ι s) := hV
    let W := V ⊓ U
    have hWU : W ≤ U := inf_le_right
    have hw : IsIso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection W.ι s) := by
      have hh := AbelianModuli.HilbertConstruction.Section.Nonvanishing.isIso_pullbackSection_comp_iff V.ι
        (X.homOfLE (show W ≤ V from inf_le_left)) s
      have hh' := hh.mp inferInstance
      rw [X.homOfLE_ι] at hh'
      exact hh'
    have hb := X.basicOpen_of_isUnit ((hiso hWU).mp hw)
    rw [X.basicOpen_res] at hb
    have hxW : x ∈ W := ⟨hxV, hx.2⟩
    exact (show x ∈ W ⊓ X.basicOpen r from hb.symm ▸ hxW).2
  · let V := X.basicOpen r
    have hV : V ≤ U := X.basicOpen_le r
    have hu : IsUnit (X.presheaf.map (homOfLE hV).op r) :=
      X.toLocallyRingedSpace.toRingedSpace.isUnit_res_basicOpen r
    exact le_inf (le_sSup ((hiso hV).mpr hu)) hV

end Construction.OverSectionLocus

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.OverSection
