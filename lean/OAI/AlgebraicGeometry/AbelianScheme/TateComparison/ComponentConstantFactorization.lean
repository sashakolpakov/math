import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ConstantGroup
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.TraceLaws
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.OverCoproduct

/-! # Component Constant Factorization -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ComponentConstantFactorization

noncomputable section

section

/-! Correspondence trace preserves maps that factor through a constant
group scheme, and these maps vanish on connected-source differences. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections OAI.AlgebraicGeometry.PELModuli.IntegralModel.ConstantBaseChange.ConstantGroupModels

variable {k : Type} [Field k] {A X : Over (Spec (.of k))} [GrpObj A] [IsCommMonObj A]

def constantGroupEvaluation : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of k)) (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest (Spec (.of k)) ⟶ A) ⟶ A :=
  AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.sectionsMap (fun a => a)

instance constantGroupEvaluation_isMonHom : IsMonHom (constantGroupEvaluation (A := A)) :=
  PELModuli.IntegralModel.ConstantBaseChange.ConstantGroupModels.sectionsMap_isMonHom (S := Spec (.of k)) (H := A)
    (MonoidHom.id (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest (Spec (.of k)) ⟶ A))

def FactorsThroughConstantGroup (f : X ⟶ A) : Prop :=
  ∃ c : X ⟶ AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of k)) (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest (Spec (.of k)) ⟶ A),
    c ≫ constantGroupEvaluation = f

theorem constantScheme_preconnected_differences {I : Type} {Y : Over (Spec (.of k))}
    [PreconnectedSpace Y.left] (f : Y ⟶ AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of k)) I)
    {T : Over (Spec (.of k))} (x y : T ⟶ Y) : x ≫ f = y ≫ f := by
  apply (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePointsEquiv (Spec (.of k)) I T).injective
  apply LocallyConstant.ext
  intro z
  exact (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePoint Y f).isLocallyConstant.apply_eq_of_preconnectedSpace (x.left z) (y.left z)

omit [GrpObj A] [IsCommMonObj A] in
theorem FactorsThroughConstantGroup.differences {f : X ⟶ A}
    (hf : FactorsThroughConstantGroup f) {Y : Over (Spec (.of k))}
    [PreconnectedSpace Y.left] (i : Y ⟶ X) {T : Over (Spec (.of k))} (x y : T ⟶ Y) :
    x ≫ i ≫ f = y ≫ i ≫ f := by
  obtain ⟨c, rfl⟩ := hf
  have he := constantScheme_preconnected_differences (i ≫ c) x y
  simpa only [Category.assoc] using congrArg (fun z => z ≫ constantGroupEvaluation) he

theorem FactorsThroughConstantGroup.trace [IsReduced X.left] [IsLocallyNoetherian X.left]
    [IsSeparated A.hom] {f : X ⟶ A} (hf : FactorsThroughConstantGroup f)
    (C : Correspondences.EtaleCorrespondence X) : FactorsThroughConstantGroup (C.algebraicTrace f) := by
  let G := AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest (Spec (.of k)) ⟶ A
  have : IsCommMonObj (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of k)) G) := ConstantGroup.constantGroup_commutative _ _
  have : IsSeparated (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of k)) G).hom := ConstantGroup.constantFieldScheme_separated G
  obtain ⟨c, rfl⟩ := hf
  exact ⟨C.algebraicTrace c, (C.algebraicTrace_postcomp c constantGroupEvaluation).symm⟩

end

/-! Componentwise constant maps factor through the actual constant group
scheme of rational points. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections

theorem overCoproduct_hom_ext {B : Scheme} {I : Type} (U : I → Over B)
    {Y : Over B} {f g : OverCoproduct.overCoproduct U ⟶ Y}
    (h : ∀ i, OverCoproduct.overCoproductι U i ≫ f = OverCoproduct.overCoproductι U i ≫ g) : f = g := by
  apply Over.OverMorphism.ext
  apply Sigma.hom_ext
  intro i
  exact congrArg Over.Hom.left (h i)

theorem factorsThroughConstantGroup_of_components
    {k : Type} [Field k] {I : Type} (U : I → Over (Spec (.of k)))
    {X A : Over (Spec (.of k))} [GrpObj A] [IsCommMonObj A]
    (e : OverCoproduct.overCoproduct U ≅ X) (f : X ⟶ A)
    (c : I → (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest (Spec (.of k)) ⟶ A))
    (hf : ∀ i, OverCoproduct.overCoproductι U i ≫ e.hom ≫ f = AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.toBase (U i) ≫ c i) :
    FactorsThroughConstantGroup f := by
  let l := e.inv ≫ OverCoproduct.overCoproductDesc U (fun i => AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.toBase (U i) ≫ AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.component (Spec (.of k)) (c i))
  refine ⟨l, ?_⟩
  apply (cancel_epi e.hom).mp
  apply overCoproduct_hom_ext U
  intro i
  calc
    _ = AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.toBase (U i) ≫ c i := by
      simp only [l, Category.assoc, e.hom_inv_id_assoc]
      rw [← Category.assoc, OverCoproduct.overCoproductι_desc, Category.assoc]
      exact congrArg (fun z => AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.toBase (U i) ≫ z) (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.component_sectionsMap (fun a => a) (c i))
    _ = _ := (hf i).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ComponentConstantFactorization
