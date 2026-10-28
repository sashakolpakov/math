import OAI.AlgebraicGeometry.Comparison.Betti.ConstantImageSections
import OAI.AlgebraicGeometry.Comparison.Betti.HomFunctor
import OAI.AlgebraicGeometry.Comparison.Betti.FlasqueHypercohomology

/-! # Image Adjoint Naturality -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ImageAdjointNaturality

noncomputable section

section

/-! Integer complexes of actual top sections identify the coefficient Hom comparison across a continuous map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

variable {X Y : TopCat.{0}}

def integerAdditiveTopGlobalComplex (K : CochainComplex (ConstantSheafSections.ComplexSheaves X) ℤ) :
    CochainComplex AddCommGrpCat.{0} ℤ :=
  ((forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0}).mapHomologicalComplex (.up ℤ)).obj
    (FlasqueHypercohomology.integerGlobalSectionsComplex K)

def integerConstantAdditiveSectionsIso (K : CochainComplex (ConstantSheafSections.ComplexSheaves X) ℤ) :
    IntegerAcyclicHomComplex.Ext.integerHomComplex (ConstantSheafSections.standardConstantSheaf X) K ≅ integerAdditiveTopGlobalComplex K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (ConstantSheafSections.constantHomSectionsLinearEquiv (K.X n)).toAddEquiv.toAddCommGrpIso)
    (fun n m _ => by
      ext g
      exact ConstantSheafSections.constantHomSectionsLinearEquiv_naturality g (K.d n m))

variable (f : Y ⟶ X) {K : CochainComplex (ConstantSheafSections.ComplexSheaves X) ℤ}
  {L : CochainComplex (ConstantSheafSections.ComplexSheaves Y) ℤ}
  (α : K ⟶ ((TopologicalSheafPullback.sheafDirectImage f).mapHomologicalComplex (.up ℤ)).obj L)

def integerTopGlobalSectionsPullback : integerAdditiveTopGlobalComplex K ⟶
    integerAdditiveTopGlobalComplex L where
  f n := (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0}).map ((α.f n).hom.app (op ⊤))
  comm' n m _ := congrArg
    (fun g => (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0}).map (g.hom.app (op ⊤))) (α.comm n m)

def directImageAdjointComplexMap : ((TopologicalSheafPullback.sheafInverseImage f).mapHomologicalComplex (.up ℤ)).obj K ⟶ L :=
  ((Complex.Adjunction.onComplexes (TopologicalSheafPullback.sheafImageAdjunction f) (.up ℤ)).homEquiv K L).symm α

theorem directImageAdjointComplexMap_f (n : ℤ) :
    (directImageAdjointComplexMap f α).f n =
      ((TopologicalSheafPullback.sheafImageAdjunction f).homEquiv (K.X n) (L.X n)).symm (α.f n) := rfl

theorem integerHomFunctorComparison_sections :
    HomFunctor.Ext.integerHomFunctorComparison (TopologicalSheafPullback.sheafInverseImage f) (TopologicalSheafPullback.constantPullbackIso f).inv
        (directImageAdjointComplexMap f α) ≫ (integerConstantAdditiveSectionsIso L).hom =
      (integerConstantAdditiveSectionsIso K).hom ≫ integerTopGlobalSectionsPullback f α := by
  apply HomologicalComplex.Hom.ext
  funext n
  ext g
  exact ConstantImageSections.constantHomSectionsLinearEquiv_directImage f (α.f n) g

end

/-! Actual commuting direct-image squares remain commuting squares under the genuine complex adjunction. -/

open _root_.CategoryTheory

variable {X Y : TopCat.{0}} (f : Y ⟶ X)
  {K K' : CochainComplex (ConstantSheafSections.ComplexSheaves X) ℤ} {L L' : CochainComplex (ConstantSheafSections.ComplexSheaves Y) ℤ}
  (α : K ⟶ ((TopologicalSheafPullback.sheafDirectImage f).mapHomologicalComplex (.up ℤ)).obj L)
  (γ : K' ⟶ ((TopologicalSheafPullback.sheafDirectImage f).mapHomologicalComplex (.up ℤ)).obj L')
  (e : K ⟶ K') (d : L ⟶ L')
  (h : e ≫ γ = α ≫ ((TopologicalSheafPullback.sheafDirectImage f).mapHomologicalComplex (.up ℤ)).map d)

include h in
theorem directImageAdjointComplexMap_square :
    ((TopologicalSheafPullback.sheafInverseImage f).mapHomologicalComplex (.up ℤ)).map e ≫ directImageAdjointComplexMap f γ =
      directImageAdjointComplexMap f α ≫ d := by
  let adj := Complex.Adjunction.onComplexes (TopologicalSheafPullback.sheafImageAdjunction f) (.up ℤ)
  apply (adj.homEquiv K L').injective
  change adj.homEquiv K L' (((TopologicalSheafPullback.sheafInverseImage f).mapHomologicalComplex (.up ℤ)).map e ≫
      (adj.homEquiv K' L').symm γ) =
    adj.homEquiv K L' ((adj.homEquiv K L).symm α ≫ d)
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact h

end

end OAI.AlgebraicGeometry.Comparison.Betti.ImageAdjointNaturality
