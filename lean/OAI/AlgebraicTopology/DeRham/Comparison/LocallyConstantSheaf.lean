import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Topology.Sheaves.LocalPredicate
import Mathlib.Topology.Sheaves.Forget
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Analysis.Complex.Basic

/-! # Locally Constant Sheaf -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf

noncomputable section

/-!
# The actual sheaf of locally constant complex-valued functions

The sections on an open set U are literally `LocallyConstant U ℂ`.
Restriction is precomposition with the open inclusion. The sheaf property
is proved from locality of local constancy, independently of differential
forms and their kernels.
-/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

universe u

/-- Locally constant complex functions with their usual restriction maps. -/
def locallyConstantPresheaf (X : TopCat.{u}) : X.Presheaf (ModuleCat.{u} ℂ) where
  obj U := ModuleCat.of ℂ (LocallyConstant U.unop ℂ)
  map i := ModuleCat.ofHom {
    toFun := fun f => ⟨fun x => f (i.unop x),
      f.isLocallyConstant.comp_continuous
        (Opens.isOpenEmbedding_of_le i.unop.le).continuous⟩
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  map_id U := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    apply LocallyConstant.ext
    intro x
    rfl
  map_comp i j := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    apply LocallyConstant.ext
    intro x
    rfl

@[simp]
theorem locallyConstantPresheaf_obj (X : TopCat.{u}) (U : Opens X) :
    (locallyConstantPresheaf X).obj (op U) = ModuleCat.of ℂ (LocallyConstant U ℂ) := rfl

@[simp]
theorem locallyConstantPresheaf_map_apply {X : TopCat.{u}} {U V : Opens X}
    (h : V ≤ U) (f : LocallyConstant U ℂ) (x : V) :
    LocallyConstant.toFun ((locallyConstantPresheaf X).map (homOfLE h).op f) x =
      f ⟨x, h x.property⟩ := rfl

/-- Local constancy is a genuinely local predicate on scalar functions. -/
def locallyConstantPredicate (X : TopCat.{u}) :
    TopCat.LocalPredicate (fun _ : X => ℂ) where
  pred f := IsLocallyConstant f
  res i f hf := hf.comp_continuous (Opens.isOpenEmbedding_of_le i.le).continuous
  locality f h := by
    intro t
    apply isOpen_iff_forall_mem_open.2
    intro x hx
    obtain ⟨V, hxV, i, hV⟩ := h x
    refine ⟨i '' ((fun y : V => f (i y)) ⁻¹' t), ?_, ?_, ?_⟩
    · rintro y ⟨z, hz, rfl⟩
      exact hz
    · exact (Opens.isOpenEmbedding_of_le i.le).isOpenMap _ (hV t)
    · exact ⟨⟨x, hxV⟩, hx, by ext; rfl⟩

/-- Unbundling local constancy changes only the packaging of the actual functions. -/
def locallyConstantSectionEquiv {X : TopCat.{u}} (U : Opens X) :
    LocallyConstant U ℂ ≃ {f : U → ℂ // IsLocallyConstant f} where
  toFun f := ⟨f, f.isLocallyConstant⟩
  invFun f := ⟨f.1, f.2⟩
  left_inv f := by cases f; rfl
  right_inv f := by cases f; rfl

/-- The underlying presheaf is the presheaf cut out by the local predicate. -/
def locallyConstantUnderlyingIso (X : TopCat.{u}) :
    locallyConstantPresheaf X ⋙ forget (ModuleCat.{u} ℂ) ≅
      TopCat.subpresheafToTypes (locallyConstantPredicate X).toPrelocalPredicate :=
  NatIso.ofComponents
    (fun U => (locallyConstantSectionEquiv U.unop).toIso)
    (by intro U V i; ext f; rfl)

/-- Compatible locally constant sections glue uniquely. -/
theorem locallyConstantPresheaf_isSheaf (X : TopCat.{u}) :
    (locallyConstantPresheaf X).IsSheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheaf_comp
    (forget (ModuleCat.{u} ℂ)) (locallyConstantPresheaf X)).2
  exact TopCat.Presheaf.isSheaf_of_iso (locallyConstantUnderlyingIso X).symm
    (TopCat.subpresheafToTypes.isSheaf (locallyConstantPredicate X))

/-- The genuine complex-module-valued sheaf of locally constant functions. -/
def locallyConstantSheaf (X : TopCat.{u}) : X.Sheaf (ModuleCat.{u} ℂ) where
  obj := locallyConstantPresheaf X
  property := locallyConstantPresheaf_isSheaf X

@[simp]
theorem locallyConstantSheaf_presheaf (X : TopCat.{u}) :
    (locallyConstantSheaf X).presheaf = locallyConstantPresheaf X := rfl

end

end OAI.AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf
