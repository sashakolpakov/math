import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleIso
import Mathlib.AlgebraicGeometry.Fiber

/-! # Line Bundle Proper Triviality -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleProperTriviality.Construction

noncomputable section

/-! A global line-bundle morphism which trivializes one proper fiber trivializes nearby fibers. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem lineBundle_morphism_isIso_near_pointwise_fiber
    {X S : Scheme.{u}} (f : X ⟶ S) [UniversallyClosed f] {M N : X.Modules}
    (hM : LineBundle.Construction.IsLineBundle M) (hN : LineBundle.Construction.IsLineBundle N) (q : M ⟶ N) (s : S)
    (hfiber : ∀ x : X, f x = s → IsIso ((Scheme.Modules.pullback (X.fromSpecResidueField x)).map q)) :
    ∃ U : S.Opens, s ∈ U ∧ IsIso ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).map q) :=
  ModuleIso.Construction.exists_baseOpen_isIso_pullback_of_fiber_in_isoLocus f q s
    (fun x hx ↦ (LineBundleIso.Construction.lineBundle_morphism_mem_isoLocus_iff hM hN q x).mpr (hfiber x hx))

theorem lineBundle_morphism_isIso_near_fiber
    {X S : Scheme.{u}} (f : X ⟶ S) [UniversallyClosed f] {M N : X.Modules}
    (hM : LineBundle.Construction.IsLineBundle M) (hN : LineBundle.Construction.IsLineBundle N) (q : M ⟶ N) (s : S)
    [hq : IsIso ((Scheme.Modules.pullback (f.fiberι s)).map q)] :
    ∃ U : S.Opens, s ∈ U ∧ IsIso ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).map q) := by
  apply lineBundle_morphism_isIso_near_pointwise_fiber f hM hN q s
  intro x hx
  subst s
  let r : Spec (X.residueField x) ⟶ f.fiber (f x) :=
    pullback.lift (X.fromSpecResidueField x) (Spec.map (f.residueFieldMap x)) (by simp)
  have hr : r ≫ f.fiberι (f x) = X.fromSpecResidueField x := pullback.lift_fst _ _ _
  have hi := ModuleIso.Construction.isIso_pullbackMap_comp (f.fiberι (f x)) r q
  exact ModuleIso.Construction.isIso_map_of_naturalIso (Scheme.Modules.pullbackCongr hr) q

theorem lineBundle_trivial_near_fiber_of_global_section
    {X S : Scheme.{u}} (f : X ⟶ S) [UniversallyClosed f] (M : X.Modules)
    (hM : LineBundle.Construction.IsLineBundle M) (q : LineBundle.Construction.structureSheafModule X ⟶ M) (s : S)
    [IsIso ((Scheme.Modules.pullback (f.fiberι s)).map q)] :
    ∃ U : S.Opens, s ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj M ≅ LineBundle.Construction.structureSheafModule (f ⁻¹ᵁ U).toScheme) := by
  obtain ⟨U, hs, hq⟩ := lineBundle_morphism_isIso_near_fiber f (LineBundle.Construction.isLineBundle_structureSheaf X) hM q s
  exact ⟨U, hs, ⟨(asIso ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).map q)).symm ≪≫
    LineBundle.Construction.pullbackStructureSheafIso (f ⁻¹ᵁ U).ι⟩⟩

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleProperTriviality.Construction
