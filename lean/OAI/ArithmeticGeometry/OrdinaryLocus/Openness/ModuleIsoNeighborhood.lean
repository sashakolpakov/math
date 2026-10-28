import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ModuleIso

/-! # Module Iso Neighborhood -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ModuleIsoNeighborhood.Construction

noncomputable section

/-! Transporting local invertibility through open immersions and trivializations. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem isIso_pullbackMap_opensRange {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {M N : Y.Modules} (q : M ⟶ N) [IsIso ((Scheme.Modules.pullback f).map q)] :
    IsIso ((Scheme.Modules.pullback f.opensRange.ι).map q) := by
  have hi := ModuleIso.Construction.isIso_pullbackMap_comp f f.isoOpensRange.inv q
  exact ModuleIso.Construction.isIso_map_of_naturalIso (Scheme.Modules.pullbackCongr f.isoOpensRange_inv_comp) q

theorem image_mem_moduleIsoLocus {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {M N : Y.Modules} (q : M ⟶ N) (x : X)
    (hx : x ∈ ModuleIso.Construction.moduleIsoLocus ((Scheme.Modules.pullback f).map q)) : f x ∈ ModuleIso.Construction.moduleIsoLocus q := by
  obtain ⟨U, hxU, hU⟩ := (ModuleIso.Construction.mem_moduleIsoLocus_iff _ x).mp hx
  have hdouble : IsIso ((Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback U.ι).map q) := hU
  have hcomp : IsIso ((Scheme.Modules.pullback (U.ι ≫ f)).map q) :=
    ModuleIso.Construction.isIso_map_of_naturalIso (Scheme.Modules.pullbackComp U.ι f) q
  apply (ModuleIso.Construction.mem_moduleIsoLocus_iff q (f x)).mpr
  refine ⟨(U.ι ≫ f).opensRange, ?_, isIso_pullbackMap_opensRange (U.ι ≫ f) q⟩
  exact ⟨⟨x, hxU⟩, rfl⟩

theorem isIso_pullbackMap_of_conjugate {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N M' N' : Y.Modules} (q : M ⟶ N) (a : M' ≅ M) (b : N ≅ N')
    [hq : IsIso ((Scheme.Modules.pullback f).map (a.hom ≫ q ≫ b.hom))] :
    IsIso ((Scheme.Modules.pullback f).map q) := by
  let F := Scheme.Modules.pullback f
  have hcomp : IsIso (F.map a.hom ≫ F.map q ≫ F.map b.hom) := by
    rw [← F.map_comp, ← F.map_comp]
    exact hq
  have hright : IsIso (F.map q ≫ F.map b.hom) := IsIso.of_isIso_comp_left (F.map a.hom) _
  exact IsIso.of_isIso_comp_right _ (F.map b.hom)

theorem mem_moduleIsoLocus_of_conjugate {Y : Scheme.{u}} {M N M' N' : Y.Modules}
    (q : M ⟶ N) (a : M' ≅ M) (b : N ≅ N') (x : Y)
    (hx : x ∈ ModuleIso.Construction.moduleIsoLocus (a.hom ≫ q ≫ b.hom)) : x ∈ ModuleIso.Construction.moduleIsoLocus q := by
  obtain ⟨U, hxU, hU⟩ := (ModuleIso.Construction.mem_moduleIsoLocus_iff _ x).mp hx
  exact (ModuleIso.Construction.mem_moduleIsoLocus_iff q x).mpr
    ⟨U, hxU, @isIso_pullbackMap_of_conjugate U.toScheme Y U.ι M N M' N' q a b hU⟩

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ModuleIsoNeighborhood.Construction
