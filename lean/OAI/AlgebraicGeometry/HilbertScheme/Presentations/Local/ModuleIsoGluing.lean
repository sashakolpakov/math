import OAI.AlgebraicGeometry.SheafCohomology.Projective.ModuleHomOverlapGluing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.ModuleIsomorphisms

/-! # Module Iso Gluing -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.ModuleIsoGluing

noncomputable section

/-! Compatible actual module isomorphisms on a covering family glue
to a global module isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.ModuleIsomorphisms OAI.AlgebraicGeometry.SheafCohomology.Projective.ModuleHomOverlapGluing

universe u v

theorem moduleMap_isIso_of_over_isIso {X : Scheme.{u}} {M N : X.Modules}
    (g : M ⟶ N) (U : X.Opens) [IsIso (g.over U)] :
    IsIso ((Scheme.Modules.pullback U.ι).map g) := by
  apply (AbelianModuli.HilbertConstruction.Power.Nonvanishing.isIso_restrict_map_iff U.ι g).mp
  let E := Scheme.Modules.overFunctorEquiv U
  have h0 : IsIso ((Scheme.Modules.overEquiv U).functor.map (g.over U)) :=
    (Scheme.Modules.overEquiv U).functor.map_isIso (g.over U)
  have he : (Scheme.Modules.restrictFunctor U.ι).map g =
      (E.app M).inv ≫ (Scheme.Modules.overEquiv U).functor.map (g.over U) ≫ (E.app N).hom := by
    apply (cancel_epi (E.app M).hom).mp
    rw [Iso.hom_inv_id_assoc]
    exact (E.hom.naturality g).symm
  rw [he]
  infer_instance

theorem exists_moduleIso_of_overlap_localIsos {X : Scheme.{u}} (M N : X.Modules)
    {ι : Type v} (U : ι → X.Opens) (hU : iSup U = ⊤)
    (W : ι → ι → X.Opens) (hl : ∀ i j, W i j ≤ U i) (hr : ∀ i j, W i j ≤ U j)
    (hW : ∀ i j, U i ⊓ U j ≤ W i j)
    (e : ∀ i, M.over (U i) ≅ N.over (U i))
    (he : ∀ i j, SheafCohomology.Projective.LinearHom.linearHomRestrict X.ringCatSheaf M N (homOfLE (hl i j)).op (e i).hom =
      SheafCohomology.Projective.LinearHom.linearHomRestrict X.ringCatSheaf M N (homOfLE (hr i j)).op (e j).hom) :
    ∃ g : M ≅ N, ∀ i, g.hom.over (U i) = (e i).hom := by
  obtain ⟨g, hg⟩ := SheafCohomology.Projective.ModuleHomOverlapGluing.exists_moduleHom_of_overlap_localMaps M N U hU W hl hr hW (fun i => (e i).hom) he
  have hi : IsIso g := by
    apply AbelianModuli.HilbertConstruction.Local.ModuleIsomorphisms.moduleMap_isIso_of_locally
    intro x
    have hx : x ∈ iSup U := by rw [hU]; trivial
    obtain ⟨i, hxi⟩ := (TopologicalSpace.Opens.mem_iSup).mp hx
    have hgi : IsIso (g.over (U i)) := by rw [hg i]; infer_instance
    exact ⟨U i, hxi, moduleMap_isIso_of_over_isIso g (U i)⟩
  exact ⟨asIso g, hg⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.ModuleIsoGluing
