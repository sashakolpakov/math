import OAI.AlgebraicGeometry.Quotients.FiniteDescent.FractionalIdealIs
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.RationalRegularityLocal

/-! # Fractional Ideal Frame -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.FractionalIdealFrame.Construction.FractionalIdealFrames

noncomputable section

/-! Local frames for sheaves of fractional ideals. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} [IsIntegral X]
variable (F : ∀ x : X, Submodule (X.presheaf.stalk x) X.functionField)

def multiply {U V : X.Opens} (hV : V ≤ U) (q : X.functionField)
    (hq : ∀ x : U, q ∈ F x) :
    Γ(X, V) →ₗ[Γ(X, V)] Γ(FractionalIdealIs.Construction.FractionalIdealSheaf.sheaf F, V) where
  toFun s := ⟨fun hv => RationalSheafIs.Construction.RationalSheaf.scalarMap V s hv * q, by
    intro x
    have : Nonempty V := ⟨x⟩
    have h := (F x).smul_mem (X.presheaf.germ V x x.2 s) (hq ⟨x, hV x.2⟩)
    change algebraMap (X.presheaf.stalk x) X.functionField
      (X.presheaf.germ V x x.2 s) * q ∈ F x at h
    rw [X.algebraMap_germ_eq_germToFunctionField] at h
    exact h⟩
  map_add' s t := by
    apply Subtype.ext
    funext hv
    change RationalSheafIs.Construction.RationalSheaf.scalarMap V (s + t) hv * q = _
    rw [map_add]
    exact add_mul _ _ _
  map_smul' r s := by
    apply Subtype.ext
    funext hv
    change RationalSheafIs.Construction.RationalSheaf.scalarMap V (r * s) hv * q =
      RationalSheafIs.Construction.RationalSheaf.scalarMap V r hv * (RationalSheafIs.Construction.RationalSheaf.scalarMap V s hv * q)
    rw [map_mul]
    exact mul_assoc _ _ _

theorem multiply_natural {U V W : X.Opens} (hV : V ≤ U) (hW : W ≤ V)
    (q : X.functionField) (hq : ∀ x : U, q ∈ F x) (s : Γ(X, V)) :
    (FractionalIdealIs.Construction.FractionalIdealSheaf.sheaf F).presheaf.map (homOfLE hW).op (multiply F hV q hq s) =
      multiply F (hW.trans hV) q hq (X.presheaf.map (homOfLE hW).op s) := by
  apply Subtype.ext
  funext hw
  exact congrArg (fun z => z * q) (congrFun (RationalSheafIs.Construction.RationalSheaf.scalar_restrict hW s) hw)

def frameMap (U : X.Opens) (q : X.functionField) (hq : ∀ x : U, q ∈ F x) :
    (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X).restrict U.ι ⟶ (FractionalIdealIs.Construction.FractionalIdealSheaf.sheaf F).restrict U.ι where
  val.app W := ModuleCat.ofHom
    (X := ((AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X).restrict U.ι).val.obj W)
    (Y := ((FractionalIdealIs.Construction.FractionalIdealSheaf.sheaf F).restrict U.ι).val.obj W) (show
    Γ((AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X).restrict U.ι, W.unop) →ₗ[Γ(U.toScheme, W.unop)]
      Γ((FractionalIdealIs.Construction.FractionalIdealSheaf.sheaf F).restrict U.ι, W.unop) from
    { toFun s := multiply F (U.ι_image_le W.unop) q hq
        (show Γ(X, U.ι ''ᵁ W.unop) from s)
      map_add' s t := (multiply F (U.ι_image_le W.unop) q hq).map_add
        (show Γ(X, U.ι ''ᵁ W.unop) from s) (show Γ(X, U.ι ''ᵁ W.unop) from t)
      map_smul' r s := by
        change Γ(X, U.ι ''ᵁ W.unop) at s
        exact (multiply F (U.ι_image_le W.unop) q hq).map_smul
          ((U.ι.appIso W.unop).inv r) s })
  val.naturality {V W} h := by
    ext s
    exact (multiply_natural F (U.ι_image_le V.unop)
      (U.ι.image_mono h.unop.le) q hq s).symm

theorem multiply_bijective {U V : X.Opens} (hV : V ≤ U)
    (q : X.functionField) (hq : ∀ x : U, q ∈ F x) (hq0 : q ≠ 0)
    (hgen : ∀ x : U, F x = Submodule.span (X.presheaf.stalk x) {q}) :
    Function.Bijective (multiply F hV q hq) := by
  constructor
  · intro s t hst
    apply RationalRegularityLocal.Construction.RationalRegularity.scalarMap_injective V
    funext hv
    exact mul_right_cancel₀ hq0 (congrFun (congrArg Subtype.val hst) hv)
  · intro t
    let r : RationalSheafIs.Construction.RationalSheaf.sections V := fun hv => t.val hv / q
    have hr (x : V) : ∃ a : X.presheaf.stalk x,
        algebraMap _ X.functionField a = r ⟨⟨x⟩⟩ := by
      have ht := t.property x
      rw [hgen ⟨x, hV x.2⟩, Submodule.mem_span_singleton] at ht
      obtain ⟨a, ha⟩ := ht
      exact ⟨a, (eq_div_iff hq0).mpr ha⟩
    obtain ⟨s, hs⟩ := RationalRegularityLocal.Construction.RationalRegularity.exists_section r hr
    refine ⟨s, Subtype.ext ?_⟩
    funext hv
    change RationalSheafIs.Construction.RationalSheaf.scalarMap V s hv * q = t.val hv
    rw [hs]
    exact div_mul_cancel₀ _ hq0

def frameIso (U : X.Opens) (q : X.functionField) (hq : ∀ x : U, q ∈ F x) (hq0 : q ≠ 0)
    (hgen : ∀ x : U, F x = Submodule.span (X.presheaf.stalk x) {q}) :
    (Scheme.Modules.pullback U.ι).obj (FractionalIdealIs.Construction.FractionalIdealSheaf.sheaf F) ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.toScheme := by
  have : IsIso (frameMap F U q hq) := by
    apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
    intro W
    apply (ConcreteCategory.isIso_iff_bijective ((frameMap F U q hq).app W)).mpr
    exact multiply_bijective F (U.ι_image_le W) q hq hq0 hgen
  exact (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app _ ≪≫
    (asIso (frameMap F U q hq)).symm ≪≫ Scheme.Modules.restrictUnitIso U.ι

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.FractionalIdealFrame.Construction.FractionalIdealFrames
