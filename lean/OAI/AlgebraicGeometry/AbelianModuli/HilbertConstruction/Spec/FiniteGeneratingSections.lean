/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleQuasicoherent.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ModulePresentations

/-! # Finite Generating Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Spec.FiniteGeneratingSections

noncomputable section

/-! A finite module of global sections on a quasicoherent affine spectrum gives actual finite global sheaf generators. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules Opposite

universe u

variable {R : CommRingCat.{u}}

theorem spec_exists_finite_generatingSections
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    [Module.Finite R Γ(M, ⊤)] :
    ∃ G : M.GeneratingSections, G.IsFiniteType := by
  let : Module.Finite R (moduleSpecΓFunctor.obj M) := by
    change Module.Finite R Γ(M, ⊤)
    infer_instance
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin
    (R := R) (M := moduleSpecΓFunctor.obj M)
  let ι := ULift.{u} (Fin n)
  let v : ι → moduleSpecΓFunctor.obj M := fun i ↦ s i.down
  have hv : Submodule.span R (Set.range v) = ⊤ := by
    have hrange : Set.range v = Set.range s := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨i.down, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨ULift.up i, rfl⟩
    rw [hrange, hs]
  let p' : ModuleCat.of R (ι →₀ R) ⟶ moduleSpecΓFunctor.obj M := by
    change ModuleCat.of R (ι →₀ R) ⟶
      ModuleCat.of R (moduleSpecΓFunctor.obj M)
    exact ModuleCat.ofHom (Finsupp.linearCombination R v)
  let : Epi p' := (ModuleCat.epi_iff_surjective p').mpr
    ((span_range_eq_top_iff_surjective_finsuppLinearCombination R).mp hv)
  let : (tilde.functor R).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction tilde.adjunction
  have hmap : Epi ((tilde.functor R).map p') :=
    Functor.map_epi (tilde.functor R) p'
  let : IsIso M.fromTildeΓ := inferInstance
  have hfrom : Epi M.fromTildeΓ := IsIso.epi_of_iso M.fromTildeΓ
  let e := tildeFinsupp (R := R) ι
  let : IsIso e.inv := e.isIso_inv
  have he : Epi e.inv := IsIso.epi_of_iso e.inv
  let f : SheafOfModules.free (R := (Spec R).ringCatSheaf) ι ⟶ M :=
    e.inv ≫ (tilde.functor R).map p' ≫ M.fromTildeΓ
  have : Epi f := by
    have hleft : Epi (e.inv ≫ (tilde.functor R).map p') :=
      epi_comp' he hmap
    have hfull : Epi ((e.inv ≫ (tilde.functor R).map p') ≫ M.fromTildeΓ) :=
      epi_comp' hleft hfrom
    exact hfull
  let G : M.GeneratingSections :=
    { I := ι
      s := M.freeHomEquiv f
      epi := by
        rw [Equiv.symm_apply_apply]
        infer_instance }
  have : G.IsFiniteType := ⟨inferInstance⟩
  exact ⟨G, inferInstance⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Spec.FiniteGeneratingSections
