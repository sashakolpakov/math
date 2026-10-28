import OAI.AlgebraicTopology.Kunneth.SimplexFormMaps
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

/-! # Simplicial Forms -/

namespace OAI.AlgebraicTopology.Kunneth.SimplicialForms

noncomputable section

/-! Restricted forms and closed forms as genuine simplicial modules. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory Opposite
open scoped Simplicial

namespace Constructions

def simplexForms (p : ℕ) : SimplicialObject (ModuleCat ℂ) where
  obj n := ModuleCat.of ℂ (RestrictedForms.Constructions.RestrictedForm (SimplexFormDomain.Constructions.coordinateSimplex n.unop.len) p)
  map θ := ModuleCat.ofHom (SimplexFormMaps.Constructions.simplexFormPullback θ.unop p)
  map_id n := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact SimplexFormMaps.Constructions.simplexFormPullback_id n.unop.len p a
  map_comp θ φ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact SimplexFormMaps.Constructions.simplexFormPullback_comp φ.unop θ.unop p a

def simplexFormDifferential (p : ℕ) : simplexForms p ⟶ simplexForms (p + 1) where
  app n := ModuleCat.ofHom (RestrictedForms.Constructions.restrictedFormD (SimplexFormDomain.Constructions.coordinateSimplex_uniqueDiffOn n.unop.len) p)
  naturality {n m} θ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact SimplexFormMaps.Constructions.simplexFormPullback_d θ.unop p a

abbrev SimplexClosedForms (n q : ℕ) :=
  LinearMap.ker (RestrictedForms.Constructions.restrictedFormD (SimplexFormDomain.Constructions.coordinateSimplex_uniqueDiffOn n) q)

def simplexClosedFormPullback {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) (q : ℕ) :
    SimplexClosedForms n q →ₗ[ℂ] SimplexClosedForms m q :=
  ((SimplexFormMaps.Constructions.simplexFormPullback f q).comp (SimplexClosedForms n q).subtype).codRestrict _ (by
    intro a
    change RestrictedForms.Constructions.restrictedFormD (SimplexFormDomain.Constructions.coordinateSimplex_uniqueDiffOn m) q
      (SimplexFormMaps.Constructions.simplexFormPullback f q a.val) = 0
    rw [SimplexFormMaps.Constructions.simplexFormPullback_d, a.property, map_zero])

@[simp] theorem simplexClosedFormPullback_val {m n : ℕ}
    (f : Fin (m + 1) → Fin (n + 1)) (q : ℕ) (a : SimplexClosedForms n q) :
    (simplexClosedFormPullback f q a).val = SimplexFormMaps.Constructions.simplexFormPullback f q a.val := rfl

def simplexClosedForms (q : ℕ) : SimplicialObject (ModuleCat ℂ) where
  obj n := ModuleCat.of ℂ (SimplexClosedForms n.unop.len q)
  map θ := ModuleCat.ofHom (simplexClosedFormPullback θ.unop q)
  map_id n := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    exact SimplexFormMaps.Constructions.simplexFormPullback_id n.unop.len q a.val
  map_comp θ φ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    exact SimplexFormMaps.Constructions.simplexFormPullback_comp φ.unop θ.unop q a.val

end Constructions

end

end OAI.AlgebraicTopology.Kunneth.SimplicialForms
