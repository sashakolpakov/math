import OAI.NumberTheory.PadicHodge.GeometricComparison.Module.SheafLocalExactness
import Mathlib.Topology.Sheaves.Sheafify
import Mathlib.CategoryTheory.Sites.Abelian
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.SheafLinear
import OAI.AlgebraicGeometry.Crystalline.Cohomology.MixedCech.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-! # Presheaf Local -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.PresheafLocal.PresheafLocalExactness

noncomputable section

/-! Exactness on a neighborhood basis gives exactness after sheafification of module presheaves. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

variable (R : Type) [CommRing R] {X : TopCat.{0}}

variable (S : ShortComplex (TopCat.Presheaf (ModuleCat.{0} R) X))
  (hlocal : ∀ (V : Opens X) (x : V), ∃ W : Opens X, W ≤ V ∧ x.val ∈ W ∧
    ∀ s : S.X₂.obj (op W), S.g.app (op W) s = 0 →
      ∃ t : S.X₁.obj (op W), S.f.app (op W) t = s)

include hlocal in
theorem stalk_exact (x : X) : (S.map (TopCat.Presheaf.stalkFunctor (ModuleCat.{0} R) x)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro y hy
  obtain ⟨U, hxU, s, rfl⟩ := S.X₂.exists_germ_eq y
  change (TopCat.Presheaf.stalkFunctor (ModuleCat.{0} R) x).map S.g (S.X₂.germ U x hxU s) = 0 at hy
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at hy
  obtain ⟨V, hxV, iVU, _, hEq⟩ := S.X₃.germ_eq x hxU hxU
    (S.g.app (op U) s) 0 (hy.trans (map_zero _).symm)
  have hzero : S.X₃.map iVU.op (S.g.app (op U) s) = 0 := by rw [hEq, map_zero]
  obtain ⟨W, hWV, hxW, hW⟩ := hlocal V ⟨x, hxV⟩
  let iWU : W ⟶ U := homOfLE hWV ≫ iVU
  let sW := S.X₂.map iWU.op s
  have hzeroW : S.X₃.map iWU.op (S.g.app (op U) s) = 0 := by
    change (S.X₃.map (iVU.op ≫ (homOfLE hWV).op)) _ = 0
    rw [S.X₃.map_comp]
    change S.X₃.map (homOfLE hWV).op (S.X₃.map iVU.op _) = 0
    rw [hzero, map_zero]
  have hsW : S.g.app (op W) sW = 0 := by
    have h := ConcreteCategory.congr_hom (S.g.naturality iWU.op) s
    exact h.trans hzeroW
  obtain ⟨t, ht⟩ := hW sW hsW
  refine ⟨S.X₁.germ W x hxW t, ?_⟩
  change (TopCat.Presheaf.stalkFunctor (ModuleCat.{0} R) x).map S.f (S.X₁.germ W x hxW t) =
    S.X₂.germ U x hxU s
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, ht]
  exact S.X₂.germ_res_apply iWU x hxW s

variable [HasSheafify (Opens.grothendieckTopology X) (ModuleCat.{0} R)]

def sheafification : TopCat.Presheaf (ModuleCat.{0} R) X ⥤ TopCat.Sheaf (ModuleCat.{0} R) X :=
  presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} R)

instance sheafification_additive : (sheafification R (X := X)).Additive where
  map_add {P Q} f g := by
    change (presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} R)).map (f + g) = _
    exact Functor.map_add _

omit hlocal in
def stalkIso (x : X) : S.map (TopCat.Presheaf.stalkFunctor (ModuleCat.{0} R) x) ≅
    (S.map (sheafification R (X := X))).map
      (TopCat.Sheaf.forget (ModuleCat.{0} R) X ⋙ TopCat.Presheaf.stalkFunctor (ModuleCat.{0} R) x) := by
  let J := Opens.grothendieckTopology X
  let F := TopCat.Presheaf.stalkFunctor (ModuleCat.{0} R) x
  let e (P : TopCat.Presheaf (ModuleCat.{0} R) X) : F.obj P ≅ F.obj (sheafify J P) := by
    let : IsIso (F.map (toSheafify J P)) := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso
      x (ModuleCat.{0} R) P
    exact asIso (F.map (toSheafify J P))
  refine ShortComplex.isoMk (e S.X₁) (e S.X₂) (e S.X₃) ?_ ?_
  · symm
    change F.map S.f ≫ F.map (toSheafify J S.X₂) =
      F.map (toSheafify J S.X₁) ≫ F.map (sheafifyMap J S.f)
    rw [← F.map_comp, ← F.map_comp, toSheafify_naturality]
  · symm
    change F.map S.g ≫ F.map (toSheafify J S.X₃) =
      F.map (toSheafify J S.X₂) ≫ F.map (sheafifyMap J S.g)
    rw [← F.map_comp, ← F.map_comp, toSheafify_naturality]

include hlocal in
theorem sheafification_exact :
    (S.map (sheafification R (X := X))).Exact := by
  rw [TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
  intro x
  exact ShortComplex.exact_of_iso (stalkIso R S x) (stalk_exact R S hlocal x)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.PresheafLocal.PresheafLocalExactness
