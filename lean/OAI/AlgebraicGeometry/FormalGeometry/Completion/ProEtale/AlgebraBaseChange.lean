import OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.Algebras
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.CategoryTheory.Adjunction.Opposites

/-! # Algebra Base Change -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.AlgebraBaseChange.Construction

noncomputable section

/-!
# Completion: the tensor adjunction on actual affine pro-étale objects

The tensor product remains weakly étale by its spectrum pullback square.
Restriction along a weakly étale covering ring map remains weakly étale
by composition. The ordinary algebra adjunction therefore restricts.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite TensorProduct

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

/-- Tensor-product base change preserves the actual geometric weakly étale condition. -/
theorem commAlgExtend_weaklyEtale (A : Algebras.Construction.ProEtaleAlgebra R) :
    Algebras.Construction.weaklyEtaleAlgebra S ((CommBaseChange.Construction.commAlgExtend f).obj A.obj) := by
  let : Algebra R S := f.toAlgebra
  change WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] A.obj))))
  rw [← pullbackSpecIso_inv_fst' R S A.obj]
  infer_instance

/-- Base change restricted to the affine objects of the actual site. -/
def proEtaleAlgebraExtend : Algebras.Construction.ProEtaleAlgebra R ⥤ Algebras.Construction.ProEtaleAlgebra S where
  obj A := ⟨(CommBaseChange.Construction.commAlgExtend f).obj A.obj, commAlgExtend_weaklyEtale f A⟩
  map g := ObjectProperty.homMk ((CommBaseChange.Construction.commAlgExtend f).map g.hom)
  map_id A := ObjectProperty.hom_ext _ ((CommBaseChange.Construction.commAlgExtend f).map_id A.obj)
  map_comp g h := ObjectProperty.hom_ext _ ((CommBaseChange.Construction.commAlgExtend f).map_comp g.hom h.hom)

variable (hf : WeaklyEtale (Spec.map (CommRingCat.ofHom f)))

include hf in
/-- Restricting scalars through a weakly étale base remains in the actual site. -/
theorem commAlgRestrict_weaklyEtale (A : Algebras.Construction.ProEtaleAlgebra S) :
    Algebras.Construction.weaklyEtaleAlgebra R ((CommBaseChange.Construction.commAlgRestrict f).obj A.obj) := by
  have := hf
  change WeaklyEtale (Spec.map (CommRingCat.ofHom f ≫
    CommRingCat.ofHom (algebraMap S A.obj)))
  rw [Spec.map_comp]
  infer_instance

/-- Restriction along a weakly étale covering ring map. -/
def proEtaleAlgebraRestrict : Algebras.Construction.ProEtaleAlgebra S ⥤ Algebras.Construction.ProEtaleAlgebra R where
  obj A := ⟨(CommBaseChange.Construction.commAlgRestrict f).obj A.obj, commAlgRestrict_weaklyEtale f hf A⟩
  map g := ObjectProperty.homMk ((CommBaseChange.Construction.commAlgRestrict f).map g.hom)

/-- The ordinary tensor-product adjunction restricted to actual affine site objects. -/
def proEtaleAlgebraAdj : proEtaleAlgebraExtend f ⊣ proEtaleAlgebraRestrict f hf :=
  (CommBaseChange.Construction.commAlgExtendRestrictAdj f).restrictFullyFaithful
    (Algebras.Construction.weaklyEtaleAlgebra R).fullyFaithfulι (Algebras.Construction.weaklyEtaleAlgebra S).fullyFaithfulι
    (Iso.refl _) (Iso.refl _)

theorem proEtaleAlgebraAdj_unit (A : Algebras.Construction.ProEtaleAlgebra R) :
    ((proEtaleAlgebraAdj f hf).unit.app A).hom =
      (CommBaseChange.Construction.commAlgExtendRestrictAdj f).unit.app A.obj := by
  simpa [proEtaleAlgebraAdj] using!
    (CommBaseChange.Construction.commAlgExtendRestrictAdj f).map_restrictFullyFaithful_unit_app
      (L := proEtaleAlgebraExtend f) (R := proEtaleAlgebraRestrict f hf)
      (Algebras.Construction.weaklyEtaleAlgebra R).fullyFaithfulι (Algebras.Construction.weaklyEtaleAlgebra S).fullyFaithfulι
      (Iso.refl _) (Iso.refl _) A

theorem proEtaleAlgebraAdj_counit (A : Algebras.Construction.ProEtaleAlgebra S) :
    ((proEtaleAlgebraAdj f hf).counit.app A).hom =
      (CommBaseChange.Construction.commAlgExtendRestrictAdj f).counit.app A.obj := by
  have h :=
    (CommBaseChange.Construction.commAlgExtendRestrictAdj f).map_restrictFullyFaithful_counit_app
      (L := proEtaleAlgebraExtend f) (R := proEtaleAlgebraRestrict f hf)
      (Algebras.Construction.weaklyEtaleAlgebra R).fullyFaithfulι (Algebras.Construction.weaklyEtaleAlgebra S).fullyFaithfulι
      (Iso.refl _) (Iso.refl _) A
  change ((proEtaleAlgebraAdj f hf).counit.app A).hom =
    𝟙 _ ≫ (CommBaseChange.Construction.commAlgExtend f).map (𝟙 ((CommBaseChange.Construction.commAlgRestrict f).obj A.obj)) ≫
      (CommBaseChange.Construction.commAlgExtendRestrictAdj f).counit.app A.obj at h
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp] at h
  exact h

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.AlgebraBaseChange.Construction
