import OAI.AlgebraicGeometry.Comparison.Betti.Godement.Functor
import OAI.AlgebraicGeometry.Comparison.Betti.FunctorialCokernel

/-! # Locality -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Godement.Locality

noncomputable section

/-! The actual Godement functor and its cokernel preserve vanishing on
an open set. The assertions concern whole neighborhoods, not single stalks. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.TopCat.Presheaf

open OAI.AlgebraicGeometry.Comparison.Betti.FunctorialCokernel.Resolution

variable {X : TopCat.{0}} {F G : TopCat.Sheaf (ModuleCat.{0} ℂ) X}

def VanishesOn (f : F ⟶ G) (U : Opens X) : Prop :=
  ∀ (V : Opens X), V ≤ U → f.hom.app (op V) = 0

theorem stalkMap_zero_of_vanishesOn (f : F ⟶ G) (U : Opens X)
    (hf : VanishesOn f U) (x : X) (hx : x ∈ U) :
    (stalkFunctor (ModuleCat.{0} ℂ) x).map f.hom = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  obtain ⟨V, hVU, hxV, s, rfl⟩ := exists_le_germ_eq F.obj t hx
  rw [stalkFunctor_map_germ_apply, hf V hVU]
  exact map_zero _

theorem vanishesOn_of_stalkMap_zero (f : F ⟶ G) (U : Opens X)
    (hf : ∀ x ∈ U, (stalkFunctor (ModuleCat.{0} ℂ) x).map f.hom = 0) : VanishesOn f U := by
  intro V hVU
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  apply section_ext G V
  intro x hx
  rw [← stalkFunctor_map_germ_apply, hf x (hVU hx)]
  change 0 = germ G.obj V x hx 0
  exact (map_zero _).symm

theorem stalkFamilyMap_vanishesOn (f : F ⟶ G) (U : Opens X) (hf : VanishesOn f U) :
    VanishesOn ((Functor.stalkFamilyFunctor X).map f) U := by
  intro V hVU
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  funext x
  change (stalkFunctor (ModuleCat.{0} ℂ) x.val).map f.hom (s x) = 0
  rw [stalkMap_zero_of_vanishesOn f U hf x.val (hVU x.property)]
  rfl

theorem quotientMap_vanishesOn (f : F ⟶ G) (U : Opens X) (hf : VanishesOn f U) :
    VanishesOn ((FunctorialCokernel.Resolution.quotientFunctor (Functor.stalkFamilyFunctor X) (Functor.stalkFamilyUnit X)).map f) U := by
  apply vanishesOn_of_stalkMap_zero
  intro x hx
  let S := TopCat.Sheaf.forget (ModuleCat.{0} ℂ) X ⋙ stalkFunctor (ModuleCat.{0} ℂ) x
  let T := Functor.stalkFamilyFunctor X
  let η := Functor.stalkFamilyUnit X
  let p := FunctorialCokernel.Resolution.quotientProjection T η
  have hp : Epi (S.map (p.app F)) := by
    change Epi (S.map (cokernel.π (η.app F)))
    infer_instance
  have hzero : S.map (T.map f) = 0 :=
    stalkMap_zero_of_vanishesOn (T.map f) U (stalkFamilyMap_vanishesOn f U hf) x hx
  change S.map ((FunctorialCokernel.Resolution.quotientFunctor T η).map f) = 0
  apply (cancel_epi (S.map (p.app F))).mp
  rw [← S.map_comp, ← p.naturality f, S.map_comp, hzero, zero_comp, comp_zero]

end

end OAI.AlgebraicGeometry.Comparison.Betti.Godement.Locality
