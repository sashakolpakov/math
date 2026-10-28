import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.AdditiveTop
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalTopSingle
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.AdditiveSections

/-! # Principal Top Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalTopCoordinates

noncomputable section

/-! Restricting the actual additive top-form unit to the original
principal-open diagram gives the native principal single-form map
through the canonical single-complex isomorphism. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe uC vC uD vD uE vE
private def compositeIso
    {C : Type uC} [Category.{vC} C] [Abelian C]
    {D : Type uD} [Category.{vD} D] [Abelian D]
    {E : Type uE} [Category.{vE} E] [Abelian E]
    (F : C ⥤ D) [F.Additive] (G : D ⥤ E) [G.Additive] (M : C) (c : ℕ) :=
  (G.mapHomologicalComplex (.up ℕ)).mapIso ((singleMapHomologicalComplex F (.up ℕ) c).app M) ≪≫
    (singleMapHomologicalComplex G (.up ℕ) c).app (F.obj M)

private theorem composite_factor
    {C : Type uC} [Category.{vC} C] [Abelian C]
    {D : Type uD} [Category.{vD} D] [Abelian D]
    {E : Type uE} [Category.{vE} E] [Abelian E]
    (F : C ⥤ D) [F.Additive] (G : D ⥤ E) [G.Additive] (M : C) (c : ℕ)
    (K : CochainComplex D ℕ) (a : (single D (.up ℕ) c).obj (F.obj M) ⟶ K) :
    (compositeIso F G M c).hom ≫ Single.CoefficientMap.map G (F.obj M) c K a =
      (G.mapHomologicalComplex (.up ℕ)).map
        ((singleMapHomologicalComplex F (.up ℕ) c).hom.app M ≫ a) := by
  simp only [compositeIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Single.CoefficientMap.map, Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]

private theorem composite_self
    {C : Type uC} [Category.{vC} C] [Abelian C]
    {D : Type uD} [Category.{vD} D] [Abelian D]
    {E : Type uE} [Category.{vE} E] [Abelian E]
    (F : C ⥤ D) [F.Additive] (G : D ⥤ E) [G.Additive] (M : C) (c : ℕ) :
    (compositeIso F G M c).hom.f c ≫ (singleObjXSelf (.up ℕ) c (G.obj (F.obj M))).hom =
      (F ⋙ G).map (singleObjXSelf (.up ℕ) c M).hom := by
  simp only [compositeIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, comp_f,
    Functor.mapHomologicalComplex_map_f, singleMapHomologicalComplex_hom_app_self,
    Functor.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Iso.map_inv_hom_id_assoc]
  rfl

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (U : X.left.affineOpens) (g : ℕ) [SmoothOfRelativeDimension g X.hom]

abbrev restriction := (Functor.whiskeringLeft
  (Principal.SectionPresheaf.Index U.val)ᵒᵖ X.left.Opensᵒᵖ AddCommGrpCat.{2}).obj
    (Principal.AdditiveSections.opens U.val U.property).op

abbrev forget := (Functor.whiskeringRight
  (Principal.SectionPresheaf.Index U.val)ᵒᵖ
  (ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) AddCommGrpCat.{2}).obj
    (AdditiveTop.Comparison.forget p k)

abbrev originalFunctor := Relative.AdditiveCechConcentration.presheaves (X := X.left) ⋙
  (Functor.whiskeringRight X.left.Opensᵒᵖ AddCommGrpCat.{0} AddCommGrpCat.{2}).obj
    AdditiveTop.Comparison.lift ⋙ restriction p k n X U

abbrev original := ((restriction p k n X U).mapHomologicalComplex (.up ℕ)).obj
  (AugmentedCech.CoefficientTotal.mapped AdditiveTop.Comparison.lift
    (AdditiveTop.Comparison.originalTop p k n X g))

abbrev native := AugmentedCech.CoefficientTotal.mapped
  (AdditiveTop.Comparison.forget p k)
  ((single _ (.up ℕ) g).obj (PrincipalTopSingle.coefficient p k n X U g))

def sourceIso : original p k n X U g ≅ native p k n X U g :=
  ((forget p k n X U).mapHomologicalComplex (.up ℕ)).mapIso
    (compositeIso (AlgebraSheafScalars.functor (Truncated.Witt.Ring p k n) X)
      (PrincipalTopSingle.diagramFunctor p k n X U)
      (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf (Truncated.Witt.Ring p k n) X g) g)

def map := ((restriction p k n X U).mapHomologicalComplex (.up ℕ)).map
  (AdditiveTop.Comparison.topUnit p k n X g)

omit [Fintype k] [CharP k p] [Smooth X.hom] [X.left.IsSeparated] in
theorem factorization : PrincipalTopCoordinates.map p k n X U g =
    (sourceIso p k n X U g).hom ≫
      ((forget p k n X U).mapHomologicalComplex (.up ℕ)).map
        (PrincipalTopSingle.map p k n X U g) := by
  have h := congrArg (fun a => ((forget p k n X U).mapHomologicalComplex (.up ℕ)).map a)
    (composite_factor (AlgebraSheafScalars.functor (Truncated.Witt.Ring p k n) X)
      (PrincipalTopSingle.diagramFunctor p k n X U)
      (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf (Truncated.Witt.Ring p k n) X g) g
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex (Truncated.Witt.Ring p k n) X)
      (IntrinsicDeRham.TopSingle.Intrinsic.sheafMap (Truncated.Witt.Ring p k n) X g))
  simp only [Functor.map_comp] at h
  exact h.symm

omit [Fintype k] [CharP k p] [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] [SmoothOfRelativeDimension g X.hom] in
theorem self : (sourceIso p k n X U g).hom.f g ≫
    (forget p k n X U).map (singleObjXSelf (.up ℕ) g
      (PrincipalTopSingle.coefficient p k n X U g)).hom =
    (originalFunctor p k n X U).map (singleObjXSelf (.up ℕ) g
      (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf (Truncated.Witt.Ring p k n) X g)).hom := by
  have h := congrArg (fun a => (forget p k n X U).map a)
    (composite_self (AlgebraSheafScalars.functor (Truncated.Witt.Ring p k n) X)
      (PrincipalTopSingle.diagramFunctor p k n X U)
      (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf (Truncated.Witt.Ring p k n) X g) g)
  simp only [Functor.map_comp] at h
  exact h

omit [Fintype k] [CharP k p] [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] [SmoothOfRelativeDimension g X.hom] in
theorem inverse_self :
    (originalFunctor p k n X U).map (singleObjXSelf (.up ℕ) g
      (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf (Truncated.Witt.Ring p k n) X g)).inv ≫
      (sourceIso p k n X U g).hom.f g =
    (forget p k n X U).map (singleObjXSelf (.up ℕ) g
      (PrincipalTopSingle.coefficient p k n X U g)).inv := by
  have h := congrArg (fun a =>
    (originalFunctor p k n X U).map (singleObjXSelf (.up ℕ) g
      (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf (Truncated.Witt.Ring p k n) X g)).inv ≫ a ≫
        (forget p k n X U).map (singleObjXSelf (.up ℕ) g
          (PrincipalTopSingle.coefficient p k n X U g)).inv)
    (self p k n X U g)
  simp only [Category.assoc, Iso.map_inv_hom_id_assoc, Iso.map_hom_inv_id] at h
  erw [Category.comp_id] at h
  exact h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalTopCoordinates
