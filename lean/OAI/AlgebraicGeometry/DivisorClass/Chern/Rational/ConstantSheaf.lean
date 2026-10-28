import OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.Obj
import Mathlib.Topology.Sheaves.LocalPredicate
import Mathlib.Topology.Sheaves.Forget

/-! # Constant Sheaf -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.ConstantSheaf.RationalCech

noncomputable section

/-! The actual rational locally constant presheaf used by ChernClass is a sheaf. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

def locallyConstantRationalPredicate (X : TopCat.{0}) :
    TopCat.LocalPredicate (fun _ : X => ℚ) where
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

def locallyConstantRationalSectionEquiv {X : TopCat.{0}} (U : Opens X) :
    LocallyConstant U ℚ ≃ {f : U → ℚ // IsLocallyConstant f} where
  toFun f := ⟨f, f.isLocallyConstant⟩
  invFun f := ⟨f.1, f.2⟩
  left_inv f := by cases f; rfl
  right_inv f := by cases f; rfl

def locallyConstantRationalUnderlyingIso (X : TopCat.{0}) :
    Cech.Obj.RationalCech.locallyConstantPresheaf X ⋙ forget (ModuleCat.{0} ℚ) ≅
      TopCat.subpresheafToTypes (locallyConstantRationalPredicate X).toPrelocalPredicate :=
  NatIso.ofComponents
    (fun U => (locallyConstantRationalSectionEquiv U.unop).toIso)
    (by intro U V i; ext f; rfl)

theorem locallyConstantRationalPresheaf_isSheaf (X : TopCat.{0}) :
    (Cech.Obj.RationalCech.locallyConstantPresheaf X).IsSheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheaf_comp
    (forget (ModuleCat.{0} ℚ)) (Cech.Obj.RationalCech.locallyConstantPresheaf X)).2
  exact TopCat.Presheaf.isSheaf_of_iso (locallyConstantRationalUnderlyingIso X).symm
    (TopCat.subpresheafToTypes.isSheaf (locallyConstantRationalPredicate X))

def locallyConstantRationalSheaf (X : TopCat.{0}) : TopCat.Sheaf (ModuleCat.{0} ℚ) X where
  obj := Cech.Obj.RationalCech.locallyConstantPresheaf X
  property := locallyConstantRationalPresheaf_isSheaf X

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.ConstantSheaf.RationalCech
