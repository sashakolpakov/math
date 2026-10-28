import OAI.AlgebraicTopology.DeRham.Comparison.SingularPresheaf
import OAI.AlgebraicTopology.Cohomology.Singular.Formulas
import Mathlib.Topology.Sheaves.Flasque

/-! # Cochain Flasque -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.CochainFlasque

noncomputable section

/-!
# Flasqueness of the actual singular cochain presheaf

In each degree, an actual cochain is a function on singular simplices.
Extending this function by zero gives a right inverse to restriction along
an injective continuous map. Thus the genuine degreewise cochain presheaf
is flasque in mathlib's sense. A separate categorical lemma records the
pointwise epimorphism hypothesis needed to pass flasqueness to a quotient.
-/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open OAI.AlgebraicTopology.DeRham.Comparison.SingularPresheaf
open scoped Simplicial

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type} [Ring R]

/-- Extend the actual simplex function by zero off the image of a continuous
map. This is a degreewise operation; no coboundary compatibility is asserted. -/
def singularCochainExtendZero (A : ModuleCat.{0} R) {X Y : TopCat.{0}}
    (f : X ⟶ Y) (n : ℕ) (c : (Basic.singularCochains A X).X n) :
    (Basic.singularCochains A Y).X n :=
  (Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj Y) A n).inv
    (Function.extend ((TopCat.toSSet.map f).app (op ⦋n⦌))
      ((Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) A n).hom c) (fun _ => 0))

/-- For an injective continuous map, restriction recovers the original
cochain from its actual extension by zero. -/
theorem singularCochainExtendZero_restrict (A : ModuleCat.{0} R) {X Y : TopCat.{0}}
    (f : X ⟶ Y) (hf : Function.Injective f) (n : ℕ)
    (c : (Basic.singularCochains A X).X n) :
    (Functor.singularPullback A f).f n (singularCochainExtendZero A f n c) = c := by
  have hsimplex : Function.Injective ((TopCat.toSSet.map f).app (op ⦋n⦌)) := by
    intro σ τ hστ
    apply (X.toSSetObjEquiv (op ⦋n⦌)).injective
    apply ContinuousMap.ext
    intro x
    apply hf
    exact congrArg (fun υ => Y.toSSetObjEquiv (op ⦋n⦌) υ x) hστ
  apply (Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) A n).toLinearEquiv.injective
  change (Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) A n).hom
      ((Functor.simplicialPullback A (TopCat.toSSet.map f)).f n
        (singularCochainExtendZero A f n c)) =
    (Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) A n).hom c
  funext σ
  rw [Formulas.degreewiseFunctionIso_pullback, singularCochainExtendZero, Iso.inv_hom_id_apply]
  exact hsimplex.extend_apply _ _ σ

/-- The extension evaluates to zero on every simplex outside the actual
image of the simplex map. -/
theorem singularCochainExtendZero_eq_zero (A : ModuleCat.{0} R) {X Y : TopCat.{0}}
    (f : X ⟶ Y) (n : ℕ) (c : (Basic.singularCochains A X).X n)
    (σ : (TopCat.toSSet.obj Y).obj (op ⦋n⦌))
    (hσ : σ ∉ Set.range ((TopCat.toSSet.map f).app (op ⦋n⦌))) :
    (Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj Y) A n).hom
      (singularCochainExtendZero A f n c) σ = 0 := by
  rw [singularCochainExtendZero, Iso.inv_hom_id_apply]
  exact Function.extend_apply' _ _ σ hσ

/-- The genuine cochain pullback is degreewise surjective along any
injective continuous map, witnessed by extension by zero. -/
theorem singularPullback_f_surjective_of_injective (A : ModuleCat.{0} R)
    {X Y : TopCat.{0}} (f : X ⟶ Y) (hf : Function.Injective f) (n : ℕ) :
    Function.Surjective ((Functor.singularPullback A f).f n) :=
  fun c => ⟨singularCochainExtendZero A f n c,
    singularCochainExtendZero_restrict A f hf n c⟩

/-- Every restriction of the actual degreewise singular cochain presheaf
is surjective. -/
theorem singularCochainDegreePresheaf_map_surjective (A : ModuleCat.{0} R)
    (X : TopCat.{0}) (n : ℕ) {U V : Opens X} (i : U ⟶ V) :
    Function.Surjective ((DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf A X n).map i.op) := by
  change Function.Surjective
    ((Functor.singularPullback A ((Opens.toTopCat X).map i)).f n)
  apply singularPullback_f_surjective_of_injective
  intro x y hxy
  exact Subtype.ext (congrArg (fun z : V => z.val) hxy)

/-- Mathlib's actual flasqueness property for the singular cochain presheaf. -/
theorem singularCochainDegreePresheaf_isFlasque (A : ModuleCat.{0} R)
    (X : TopCat.{0}) (n : ℕ) :
    TopCat.Presheaf.IsFlasque (DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf A X n) where
  epi {_U _V} i :=
    (ModuleCat.epi_iff_surjective _).mpr
      (singularCochainDegreePresheaf_map_surjective A X n i.unop)

/-- A pointwise epimorphic image of a flasque presheaf is flasque. The
pointwise epimorphism condition is explicit and essential. -/
theorem presheaf_isFlasque_of_pointwise_epi {C : Type*} [Category C]
    {X : TopCat.{0}} {F G : X.Presheaf C} (α : F ⟶ G)
    [TopCat.Presheaf.IsFlasque F]
    (hα : ∀ U : (Opens X)ᵒᵖ, Epi (α.app U)) :
    TopCat.Presheaf.IsFlasque G where
  epi {U V} i := by
    have := hα V
    have : Epi (α.app U ≫ G.map i) := by
      rw [← α.naturality i]
      infer_instance
    exact epi_of_epi (α.app U) (G.map i)

end

end OAI.AlgebraicTopology.Cohomology.Singular.CochainFlasque
