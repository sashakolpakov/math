import Mathlib.Topology.Sheaves.LocalPredicate
import Mathlib.Topology.Sheaves.Forget
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Algebra.Category.Grp.Limits

/-! # Integral Constant Sheaf -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.IntegralConstantSheaf

noncomputable section

/-! The actual integral constant sheaf, as locally constant integer-valued functions. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def locallyConstantIntegerPresheaf (X : TopCat.{0}) : X.Presheaf AddCommGrpCat where
  obj U := AddCommGrpCat.of (LocallyConstant U.unop ℤ)
  map i := AddCommGrpCat.ofHom {
    toFun f := ⟨fun x => f (i.unop x), f.isLocallyConstant.comp_continuous
      (Opens.isOpenEmbedding_of_le i.unop.le).continuous⟩
    map_zero' := rfl
    map_add' := fun _ _ => rfl }
  map_id U := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro f
    apply LocallyConstant.ext
    intro x
    rfl
  map_comp i j := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro f
    apply LocallyConstant.ext
    intro x
    rfl

def locallyConstantIntegerPredicate (X : TopCat.{0}) : TopCat.LocalPredicate (fun _ : X => ℤ) where
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

def locallyConstantIntegerSectionEquiv {X : TopCat.{0}} (U : Opens X) :
    LocallyConstant U ℤ ≃ {f : U → ℤ // IsLocallyConstant f} where
  toFun f := ⟨f, f.isLocallyConstant⟩
  invFun f := ⟨f.1, f.2⟩
  left_inv f := by cases f; rfl
  right_inv f := by cases f; rfl

def locallyConstantIntegerUnderlyingIso (X : TopCat.{0}) :
    locallyConstantIntegerPresheaf X ⋙ forget AddCommGrpCat ≅
    TopCat.subpresheafToTypes (locallyConstantIntegerPredicate X).toPrelocalPredicate :=
  NatIso.ofComponents (fun U => (locallyConstantIntegerSectionEquiv U.unop).toIso)
    (by intro U V i; ext f; rfl)

theorem locallyConstantIntegerPresheaf_isSheaf (X : TopCat.{0}) :
    (locallyConstantIntegerPresheaf X).IsSheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheaf_comp
    (forget AddCommGrpCat) (locallyConstantIntegerPresheaf X)).2
  exact TopCat.Presheaf.isSheaf_of_iso (locallyConstantIntegerUnderlyingIso X).symm
    (TopCat.subpresheafToTypes.isSheaf (locallyConstantIntegerPredicate X))

def integralConstantSheaf (X : TopCat.{0}) : TopCat.Sheaf AddCommGrpCat X where
  obj := locallyConstantIntegerPresheaf X
  property := locallyConstantIntegerPresheaf_isSheaf X

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.IntegralConstantSheaf
