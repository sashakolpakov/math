import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
import Mathlib.RingTheory.Noetherian.Basic

/-! # Finite Projectives -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.FiniteProjectives

noncomputable section

/-! Finitely generated modules have finite free presentations. This gives
enough projectives in their category, and its inclusion in all modules
preserves projective objects. -/

open _root_.CategoryTheory

universe u

variable (R : Type u) [CommRing R]

abbrev inclusion : FGModuleCat.{u} R ⥤ ModuleCat.{u} R := forget₂ _ _

theorem projective_of_module (M : FGModuleCat.{u} R) [Module.Projective R M] : Projective M :=
  (inclusion R).projective_of_map_projective
    (ModuleCat.projective_of_categoryTheory_projective M.obj)

def finiteFreePresentation (M : FGModuleCat.{u} R) : ProjectivePresentation M := Classical.choice (by
  obtain ⟨P, _, _, _, _, f, hf⟩ := Module.exists_finite_presentation R M
  let f' : FGModuleCat.of R P ⟶ M := FGModuleCat.ofHom f
  let : Epi ((inclusion R).map f') := (ModuleCat.epi_iff_surjective _).mpr hf
  let : Epi f' := (inclusion R).epi_of_epi_map inferInstance
  exact ⟨{ p := FGModuleCat.of R P, projective := projective_of_module R _, f := f' }⟩)

instance : EnoughProjectives (FGModuleCat.{u} R) where
  presentation M := ⟨finiteFreePresentation R M⟩

instance : (inclusion R).PreservesProjectiveObjects where
  projective_obj {M} hM := by
    let : Projective M := hM
    obtain ⟨P, _, _, _, _, f, hf⟩ := Module.exists_finite_presentation R M
    let f' : FGModuleCat.of R P ⟶ M := FGModuleCat.ofHom f
    let : Epi ((inclusion R).map f') := (ModuleCat.epi_iff_surjective _).mpr hf
    let : Epi f' := (inclusion R).epi_of_epi_map inferInstance
    let s := Projective.factorThru (𝟙 M) f'
    have hs : f.comp s.hom.hom = LinearMap.id :=
      congrArg (fun g : M ⟶ M => g.hom.hom) (Projective.factorThru_comp (𝟙 M) f')
    let : Module.Projective R M := Module.Projective.of_split s.hom.hom f hs
    exact ModuleCat.projective_of_categoryTheory_projective M.obj

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.FiniteProjectives
