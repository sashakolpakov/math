import OAI.AlgebraicTopology.Cohomology.Singular.Augmentation
import Mathlib.Topology.Sheaves.LocalPredicate
import Mathlib.Topology.Sheaves.Forget

/-! # Locally Constant Module Sheaf -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LocallyConstantModuleSheaf

noncomputable section

/-! The actual locally constant sheaf for a coefficient module, with
pointwise coefficient maps and its singular degree-zero augmentation. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

open OAI.AlgebraicTopology.Cohomology.Singular.Augmentation OAI.AlgebraicTopology.Cohomology.Singular.Augmentation.Comparison

variable {R : Type} [Ring R] (M : ModuleCat.{0} R) (X : TopCat.{0})

abbrev coefficientLocallyConstantPresheaf : X.Presheaf (ModuleCat.{0} R) where
  obj U := ModuleCat.of R (LocallyConstant U.unop M)
  map i := ModuleCat.ofHom {
    toFun := fun f => ⟨fun x => f (i.unop x),
      f.isLocallyConstant.comp_continuous (Opens.isOpenEmbedding_of_le i.unop.le).continuous⟩
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  map_id _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    apply LocallyConstant.ext
    intro x
    rfl
  map_comp _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    apply LocallyConstant.ext
    intro x
    rfl

def coefficientLocallyConstantPredicate : TopCat.LocalPredicate (fun _ : X => M) where
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

def coefficientLocallyConstantSectionEquiv (U : Opens X) :
    LocallyConstant U M ≃ {f : U → M // IsLocallyConstant f} where
  toFun f := ⟨f, f.isLocallyConstant⟩
  invFun f := ⟨f.1, f.2⟩
  left_inv f := by cases f; rfl
  right_inv f := by cases f; rfl

def coefficientLocallyConstantUnderlyingIso :
    coefficientLocallyConstantPresheaf M X ⋙ forget (ModuleCat.{0} R) ≅
      TopCat.subpresheafToTypes (coefficientLocallyConstantPredicate M X).toPrelocalPredicate :=
  NatIso.ofComponents (fun U => (coefficientLocallyConstantSectionEquiv M X U.unop).toIso)
    (by intro U V i; ext f; rfl)

theorem coefficientLocallyConstantPresheaf_isSheaf :
    (coefficientLocallyConstantPresheaf M X).IsSheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheaf_comp
    (forget (ModuleCat.{0} R)) (coefficientLocallyConstantPresheaf M X)).2
  exact TopCat.Presheaf.isSheaf_of_iso (coefficientLocallyConstantUnderlyingIso M X).symm
    (TopCat.subpresheafToTypes.isSheaf (coefficientLocallyConstantPredicate M X))

def coefficientLocallyConstantSheaf : TopCat.Sheaf (ModuleCat.{0} R) X where
  obj := coefficientLocallyConstantPresheaf M X
  property := coefficientLocallyConstantPresheaf_isSheaf M X

def coefficientLocallyConstantAugmentation :
    coefficientLocallyConstantPresheaf M X ⟶ AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X 0 where
  app U := AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero M (TopCat.of U.unop)
  naturality _ _ i := AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero_naturality M ((Opens.toTopCat X).map i.unop)

def coefficientLocallyConstantSheafMap {N : ModuleCat.{0} R} (f : M ⟶ N) :
    coefficientLocallyConstantSheaf M X ⟶ coefficientLocallyConstantSheaf N X where
  hom := {
    app U := ModuleCat.ofHom {
      toFun a := ⟨fun x => f (a x), a.isLocallyConstant.comp _⟩
      map_add' a b := by ext x; exact map_add f.hom (a x) (b x)
      map_smul' r a := by ext x; exact map_smul f.hom r (a x) }
    naturality _ _ _ := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      apply LocallyConstant.ext
      intro x
      rfl }

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LocallyConstantModuleSheaf
