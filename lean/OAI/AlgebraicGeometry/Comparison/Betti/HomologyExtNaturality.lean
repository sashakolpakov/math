import OAI.AlgebraicGeometry.Comparison.Betti.InjectiveHomologyExt
import OAI.AlgebraicGeometry.Comparison.Betti.CochainClasses

/-! # Homology Ext Naturality -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.HomologyExtNaturality

noncomputable section

/-! Normalization and naturality of the actual injective-resolution cohomology comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian Opposite

universe w v u t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {R : Type t} [CommRing R] [Linear R C]
  {X Y : C} (I : InjectiveResolution Y)

theorem homologyExtLinearEquiv_class (n : ℕ) (f : X ⟶ I.cocomplex.X n)
    (hf : f ≫ I.cocomplex.d n (n + 1) = 0) :
    InjectiveHomologyExt.homologyExtLinearEquiv (R := R) I n
      (CochainClasses.Homology.cochainClass (InjectiveHomologyExt.homSectionsComplex (R := R) I X) n f hf) =
        I.extMk f (n + 1) rfl hf := by
  let K := InjectiveHomologyExt.homSectionsComplex (R := R) I X
  let S := K.sc' (n - 1) n (n + 1)
  let e := CochainClasses.Homology.adjacentHomologyIso K n
  let q := (Submodule.quotEquivOfEq _ _ (InjectiveHomologyExt.cocycleToExt_kernel (R := R) (X := X) I n).symm).trans
    ((InjectiveHomologyExt.cocycleToExt (R := R) (X := X) I n).quotKerEquivOfSurjective (InjectiveHomologyExt.cocycleToExt_surjective I n))
  change q (S.moduleCatHomologyIso.hom
    (e.hom (e.inv (Module.HomologyClasses.homologyClass S f hf)))) = _
  have he : e.hom (e.inv (Module.HomologyClasses.homologyClass S f hf)) = Module.HomologyClasses.homologyClass S f hf :=
    e.toLinearEquiv.apply_symm_apply _
  rw [he]
  erw [Module.HomologyClasses.homologyClass_quotient]
  have hq : S.moduleCatHomologyIso.hom
      (S.moduleCatHomologyIso.inv (Submodule.Quotient.mk ⟨f, hf⟩)) = Submodule.Quotient.mk ⟨f, hf⟩ :=
    S.moduleCatHomologyIso.toLinearEquiv.apply_symm_apply _
  rw [hq]
  change (InjectiveHomologyExt.cocycleToExt (R := R) (X := X) I n).quotKerEquivOfSurjective
    (InjectiveHomologyExt.cocycleToExt_surjective I n)
    ((Submodule.quotEquivOfEq _ _ (InjectiveHomologyExt.cocycleToExt_kernel (R := R) (X := X) I n).symm)
      (Submodule.Quotient.mk ⟨f, hf⟩)) = _
  rw [Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]
  rfl

variable {I} {Y' : C} {J : InjectiveResolution Y'} {u : Y ⟶ Y'}

def homSectionsResolutionMap (φ : InjectiveResolution.Hom I J u) :
    InjectiveHomologyExt.homSectionsComplex (R := R) I X ⟶ InjectiveHomologyExt.homSectionsComplex (R := R) J X :=
  (((linearCoyoneda R C).obj (op X)).mapHomologicalComplex (ComplexShape.up ℕ)).map φ.hom

theorem homologyExtLinearEquiv_naturality (φ : InjectiveResolution.Hom I J u)
    (n : ℕ) (a : (InjectiveHomologyExt.homSectionsComplex (R := R) I X).homology n) :
    InjectiveHomologyExt.homologyExtLinearEquiv (R := R) J n
        (HomologicalComplex.homologyMap (homSectionsResolutionMap (R := R) (X := X) φ) n a) =
      (InjectiveHomologyExt.homologyExtLinearEquiv (R := R) I n a).comp (Ext.mk₀ u) (add_zero n) := by
  obtain ⟨f, hf, rfl⟩ := CochainClasses.Homology.cochainClass_surjective (InjectiveHomologyExt.homSectionsComplex (R := R) I X) n a
  rw [CochainClasses.Homology.cochainClass_naturality]
  erw [homologyExtLinearEquiv_class,
    homologyExtLinearEquiv_class]
  exact (InjectiveResolution.extMk_comp_mk₀ f (n + 1) rfl hf φ).symm

variable (I) {X' : C}

def homSectionsPrecompose (v : X' ⟶ X) :
    InjectiveHomologyExt.homSectionsComplex (R := R) I X ⟶ InjectiveHomologyExt.homSectionsComplex (R := R) I X' :=
  (((linearCoyoneda R C).map v.op).mapHomologicalComplex (ComplexShape.up ℕ)).app I.cocomplex

theorem homologyExtLinearEquiv_precompose (v : X' ⟶ X)
    (n : ℕ) (a : (InjectiveHomologyExt.homSectionsComplex (R := R) I X).homology n) :
    InjectiveHomologyExt.homologyExtLinearEquiv (R := R) I n
        (HomologicalComplex.homologyMap (homSectionsPrecompose (R := R) I v) n a) =
      (Ext.mk₀ v).comp (InjectiveHomologyExt.homologyExtLinearEquiv (R := R) I n a) (zero_add n) := by
  obtain ⟨f, hf, rfl⟩ := CochainClasses.Homology.cochainClass_surjective (InjectiveHomologyExt.homSectionsComplex (R := R) I X) n a
  rw [CochainClasses.Homology.cochainClass_naturality]
  erw [homologyExtLinearEquiv_class, homologyExtLinearEquiv_class]
  exact (I.mk₀_comp_extMk f (n + 1) rfl hf v).symm

end

end OAI.AlgebraicGeometry.Comparison.Betti.HomologyExtNaturality
