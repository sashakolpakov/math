import OAI.AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Topology.Sheaves.LocallySurjective

/-! # Constant Locally Constant -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.ConstantLocallyConstant

noncomputable section

/-!
# The constant complex sheaf is the sheaf of locally constant functions

The constant-presheaf map sends a scalar to its constant function. We prove
this map locally injective and locally surjective on the actual topology of
the space, and use mathlib's sheafification theorem to obtain the isomorphism.
There is no assumed cohomological or de Rham comparison.

The sheafification identification is stated for small topological spaces
(`TopCat.{0}`), so its constant coefficient object is literally `ℂ`.
-/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

/-- A locally constant function on an open set is constant on an actual open
neighborhood in the ambient space. -/
theorem locallyConstant_exists_constant_neighborhood
    {X Y : Type*} [TopologicalSpace X] (U : Opens X)
    (f : LocallyConstant U Y) (x : U) :
    ∃ (V : Opens X) (hVU : V ≤ U), (x : X) ∈ V ∧
      ∀ y : V, f ⟨y, hVU y.property⟩ = f x := by
  let s : Set U := {y | f y = f x}
  let V : Opens X := ⟨Subtype.val '' s,
    U.isOpen.isOpenMap_subtype_val s (f.isLocallyConstant.isOpen_fiber (f x))⟩
  have hVU : V ≤ U := by
    rintro y ⟨z, _, rfl⟩
    exact z.property
  refine ⟨V, hVU, ⟨x, rfl, rfl⟩, ?_⟩
  intro y
  obtain ⟨z, hz, hzy⟩ := y.property
  have heq : z = (⟨y, hVU y.property⟩ : U) := Subtype.ext hzy
  change f z = f x at hz
  simpa only [heq] using hz

variable (X : TopCat.{0})

/-- The actual constant complex-valued presheaf. -/
def constantComplexPresheaf : X.Presheaf (ModuleCat.{0} ℂ) :=
  (Functor.const (Opens X)ᵒᵖ).obj (ModuleCat.of ℂ ℂ)

/-- A scalar maps to the corresponding constant locally constant function. -/
def constantToLocallyConstant :
    constantComplexPresheaf X ⟶ LocallyConstantSheaf.locallyConstantPresheaf X where
  app U := ModuleCat.ofHom (LocallyConstant.constₗ (X := U.unop) ℂ)
  naturality U V i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    apply LocallyConstant.ext
    intro x
    rfl

@[simp]
theorem constantToLocallyConstant_apply (U : Opens X) (c : ℂ) (x : U) :
    LocallyConstant.toFun
      ((constantToLocallyConstant X).app (op U) c : LocallyConstant U ℂ) x = c := rfl

/-- Constants whose functions agree agree locally, including over the empty
open set where the covering condition is vacuous. -/
instance constantToLocallyConstant_isLocallyInjective :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (constantToLocallyConstant X) where
  equalizerSieve_mem {U} a b hab := by
    intro x hx
    have heq : a = b :=
      congrArg (fun f : LocallyConstant U.unop ℂ => f ⟨x, hx⟩) hab
    refine ⟨U.unop, 𝟙 _, ?_, hx⟩
    change a = b
    exact heq

/-- Every locally constant section is locally the image of a constant scalar. -/
instance constantToLocallyConstant_isLocallySurjective :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (constantToLocallyConstant X) := by
  apply (TopCat.Presheaf.isLocallySurjective_iff (constantToLocallyConstant X)).2
  intro U f x hx
  let g : LocallyConstant U ℂ := f
  obtain ⟨V, hVU, hxV, hV⟩ :=
    locallyConstant_exists_constant_neighborhood U g ⟨x, hx⟩
  refine ⟨V, hVU, ⟨g ⟨x, hx⟩, ?_⟩, hxV⟩
  apply LocallyConstant.ext
  intro y
  change g ⟨x, hx⟩ = g ⟨y, hVU y.property⟩
  exact (hV y).symm

/-- The actual constant-presheaf map becomes an isomorphism on sheafification. -/
instance constantToLocallyConstant_sheafify_isIso :
    IsIso ((presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)).map
      (constantToLocallyConstant X)) :=
  ((Opens.grothendieckTopology X).W_iff (constantToLocallyConstant X)).mp
    ((Opens.grothendieckTopology X).W_of_isLocallyBijective (constantToLocallyConstant X))

/-- Mathlib's constant complex sheaf is canonically the actual sheaf of
locally constant complex-valued functions. -/
def constantSheafLocallyConstantIso :
    (constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)).obj
        (ModuleCat.of ℂ ℂ) ≅ LocallyConstantSheaf.locallyConstantSheaf X := by
  let f := (presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)).map
    (constantToLocallyConstant X)
  let hf : IsIso f := constantToLocallyConstant_sheafify_isIso X
  exact @asIso _ _ _ _ f hf ≪≫
    (sheafificationIso (LocallyConstantSheaf.locallyConstantSheaf X)).symm

/-- The isomorphism is the one induced by constant functions under the
universal property of sheafification. -/
@[reassoc]
theorem constantSheafLocallyConstantIso_fac :
    CategoryTheory.toSheafify (Opens.grothendieckTopology X) (constantComplexPresheaf X) ≫
      (constantSheafLocallyConstantIso X).hom.hom = constantToLocallyConstant X := by
  change CategoryTheory.toSheafify (Opens.grothendieckTopology X) _ ≫
    (sheafifyMap (Opens.grothendieckTopology X) (constantToLocallyConstant X) ≫
      (isoSheafify (Opens.grothendieckTopology X)
        (LocallyConstantSheaf.locallyConstantPresheaf_isSheaf X)).inv) = _
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc,
    ← isoSheafify_hom (Opens.grothendieckTopology X) (LocallyConstantSheaf.locallyConstantPresheaf_isSheaf X),
    Iso.hom_inv_id, Category.comp_id]

end

end OAI.AlgebraicTopology.DeRham.Comparison.ConstantLocallyConstant
