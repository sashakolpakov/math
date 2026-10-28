import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PoleLine
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PoleIdealEq
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModuleRestrictionIs

/-! # Pole Section Eq -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.PoleSectionEq.Construction.PoleSection

noncomputable section

/-! The canonical pole-divisor section is nonvanishing precisely on the regular locus. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsIntegral X]
variable (f : X ⟶ Spec (.of K)) [Smooth f] (r : X.functionField)

theorem restrict_eq_frameMap (U : X.Opens) :
    (Scheme.Modules.restrictFunctor U.ι).map (PoleLine.Construction.PoleLineBundle.canonicalSection f r) =
      FractionalIdealFrame.Construction.FractionalIdealFrames.frameMap (PoleLine.Construction.PoleLineBundle.stalkModules r) U 1
        (fun _ => InverseIdealEq.Construction.InverseIdeal.one_mem _) := by
  rfl

theorem pullback_isIso_of_regular (U : X.Opens)
    (h : ∀ x : U, ∃ a : X.presheaf.stalk x, algebraMap _ X.functionField a = r) :
    IsIso ((Scheme.Modules.pullback U.ι).map (PoleLine.Construction.PoleLineBundle.canonicalSection f r)) := by
  apply (AbelianModuli.HilbertConstruction.Power.Nonvanishing.isIso_restrict_map_iff U.ι _).mp
  rw [restrict_eq_frameMap]
  have hgen (x : U) : PoleLine.Construction.PoleLineBundle.stalkModules r x =
      Submodule.span (X.presheaf.stalk x) {(1 : X.functionField)} := by
    change InverseIdealEq.Construction.InverseIdeal.module (DenominatorIdealEq.Construction.DenominatorIdeal.ideal r) = _
    rw [(PoleIdealEq.Construction.PoleIdeal.denominator_eq_top r).mpr (h x), PoleIdealEq.Construction.PoleIdeal.inverse_top]
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro V
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact FractionalIdealFrame.Construction.FractionalIdealFrames.multiply_bijective (PoleLine.Construction.PoleLineBundle.stalkModules r)
    (U.ι_image_le V) 1 (fun x => InverseIdealEq.Construction.InverseIdeal.one_mem _) one_ne_zero hgen

theorem ideal_eq_top_of_app_isIso (U : X.affineOpens) [Nonempty U.1]
    (a : Γ(X, U)) (ha : (DenominatorSheafEq.Construction.DenominatorSheaf.data r).ideal U = Ideal.span {a})
    [IsIso ((PoleLine.Construction.PoleLineBundle.canonicalSection f r).app U.1)] :
    (DenominatorSheafEq.Construction.DenominatorSheaf.data r).ideal U = ⊤ := by
  let q : X.functionField := (X.germToFunctionField U.1 a)⁻¹
  let t : Γ((PoleLine.Construction.PoleLineBundle.lineBundle f r).sheaf, U.1) := ⟨fun _ => q, by
    intro x
    rw [PoleLine.Construction.PoleLineBundle.generator r U a ha x]
    exact Submodule.mem_span_singleton_self _⟩
  obtain ⟨s, hs⟩ := ((ConcreteCategory.isIso_iff_bijective
    ((PoleLine.Construction.PoleLineBundle.canonicalSection f r).app U.1)).mp inferInstance).2 t
  change Γ(X, U.1) at s
  have hs' := congrFun (congrArg Subtype.val hs) ⟨inferInstance⟩
  change X.germToFunctionField U.1 s * 1 = q at hs'
  rw [mul_one] at hs'
  have hne : X.germToFunctionField U.1 a ≠ 0 := by
    simpa only [map_zero] using (X.germToFunctionField_injective U.1).ne
      (DenominatorLine.Construction.DenominatorLineBundle.generator_ne_zero r U a ha)
  have hu : IsUnit a := isUnit_iff_exists_inv.mpr ⟨s, by
    apply X.germToFunctionField_injective U.1
    rw [map_mul, map_one, hs']
    exact mul_inv_cancel₀ hne⟩
  rw [ha, Ideal.span_singleton_eq_top.mpr hu]

theorem mem_nonvanishing_of_regular (x : X)
    (h : ∃ a : X.presheaf.stalk x, algebraMap _ X.functionField a = r) :
    x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (PoleLine.Construction.PoleLineBundle.canonicalSection f r) := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨U, hxU, s, hs⟩ := X.presheaf.exists_germ_eq a
  change X.Opens at U
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  have hr : X.germToFunctionField U s = r := by
    rw [← X.algebraMap_germ_eq_germToFunctionField hxU s, hs, ha]
  have hreg (y : U) : ∃ b : X.presheaf.stalk y, algebraMap _ X.functionField b = r :=
    ⟨X.presheaf.germ U y y.2 s, (X.algebraMap_germ_eq_germToFunctionField y.2 s).trans hr⟩
  have := pullback_isIso_of_regular f r U hreg
  exact TopologicalSpace.Opens.mem_sSup.mpr ⟨U,
    (AbelianModuli.HilbertConstruction.Section.Nonvanishing.isIso_pullbackSection_iff U.ι _).mpr inferInstance, hxU⟩

theorem mem_nonvanishing_iff_regular (x : X) :
    x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (PoleLine.Construction.PoleLineBundle.canonicalSection f r) ↔
      ∃ a : X.presheaf.stalk x, algebraMap _ X.functionField a = r := by
  constructor
  · intro hx
    obtain ⟨V, hV, hxV⟩ := TopologicalSpace.Opens.mem_sSup.mp hx
    change X.Opens at V
    have : IsIso ((Scheme.Modules.pullback V.ι).map (PoleLine.Construction.PoleLineBundle.canonicalSection f r)) :=
      (AbelianModuli.HilbertConstruction.Section.Nonvanishing.isIso_pullbackSection_iff V.ι _).mp hV
    obtain ⟨U, hxU, hUV, a, ha⟩ := DenominatorNeighborhoodLe.Construction.DenominatorNeighborhood.exists_principal_le f r V ⟨x, hxV⟩
    have : Nonempty U.1 := ⟨⟨x, hxU⟩⟩
    change (DenominatorSheafEq.Construction.DenominatorSheaf.data r).ideal U = Ideal.span {a} at ha
    have := ModuleRestrictionIs.Construction.ModuleRestriction.isIso_app (PoleLine.Construction.PoleLineBundle.canonicalSection f r) V U.1 hUV
    have ht := ideal_eq_top_of_app_isIso f r U a ha
    apply (PoleIdealEq.Construction.PoleIdeal.denominator_eq_top r).mp
    rw [← DenominatorStalkIs.Construction.DenominatorStalk.map_stalk r U ⟨x, hxU⟩, ht, Ideal.map_top]
  · exact mem_nonvanishing_of_regular f r x

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.PoleSectionEq.Construction.PoleSection
