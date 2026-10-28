import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.GlobalModuleGenerators
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections

/-! # Module Zero Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A globally generated module sheaf with zero global sections is zero. Finite global generation also descends along an actual scheme isomorphism. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem Finite.GlobalModuleGenerators.HasFiniteGlobalGenerators.isZero_of_sections_subsingleton
    {X : Scheme.{u}} (M : X.Modules) (hM : Finite.GlobalModuleGenerators.HasFiniteGlobalGenerators M)
    (hsections : Subsingleton Γ(M, ⊤)) : IsZero M := by
  obtain ⟨ι, _, s, hs⟩ := hM
  have : Epi (Sigma.desc s) := hs
  have hzero : Sigma.desc s = 0 := by
    apply Sigma.hom_ext
    intro i
    rw [Sigma.ι_comp_desc, comp_zero]
    apply (Global.Sections.moduleSectionHomEquiv M).injective
    exact hsections.elim _ _
  apply (IsZero.iff_id_eq_zero M).mpr
  apply (cancel_epi (Sigma.desc s)).mp
  rw [Category.comp_id, comp_zero, hzero]

theorem Finite.GlobalModuleGenerators.HasFiniteGlobalGenerators.of_pullback_iso
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsIso f] (M : X.Modules)
    (hM : Finite.GlobalModuleGenerators.HasFiniteGlobalGenerators ((Scheme.Modules.pullback f).obj M)) :
    Finite.GlobalModuleGenerators.HasFiniteGlobalGenerators M := by
  let e : (Scheme.Modules.pullback (inv f)).obj ((Scheme.Modules.pullback f).obj M) ≅ M :=
    (Scheme.Modules.pullbackComp (inv f) f).app M ≪≫
      (Scheme.Modules.pullbackCongr (asIso f).inv_hom_id).app M ≪≫
        (Scheme.Modules.pullbackId X).app M
  exact (hM.pullback (inv f)).of_iso e

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
