import OAI.AlgebraicGeometry.PELModuli.IntegralModel.EmbeddedGroupParameters
import OAI.AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety

/-! # Embedded Group Coefficients -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.EmbeddedGroupCoefficients.Abelian

noncomputable section

section

/-! Actual smooth proper commutative group models over finite rational
coefficient rings, retaining a projective embedding and the complex group. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.EmbeddedGroupParameters.Coefficients

def abelianProjectiveEmbedding (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    A.toOver ⟶ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace ℂ A.variety.presentation.ambientDimension :=
  A.variety.presentation.projective.toOverHom

instance abelianProjectiveEmbedding_closed (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    IsClosedImmersion (abelianProjectiveEmbedding A).left :=
  A.variety.presentation.projective.closedImmersion

/-- The coefficient family and all its group laws are constructed from the
original abelian variety. Geometric connectedness of the family is a separate
spreading obligation. -/
theorem abelian_variety_has_embedded_group_coefficient_model (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    ∃ (D : AlgebraicGeometry.PELModuli.IntegralModel.SmoothProjectiveParameters.Coefficients.EmbeddedCoefficientModel ℚ ℂ A.toOver A.variety.presentation.ambientDimension)
      (groupD : GrpObj D.toModel.model),
      Smooth D.toModel.model.hom ∧ IsProper D.toModel.model.hom ∧
      (letI := groupD; IsCommMonObj D.toModel.model) ∧
      (letI := groupD
       letI : GrpObj ((Over.pullback (Models.CoefficientSystem.Constructions.Foundations.genericBaseMap ℚ ℂ D.toModel.coefficients)).obj
         D.toModel.model) := Functor.grpObjObj
           (F := Over.pullback (Models.CoefficientSystem.Constructions.Foundations.genericBaseMap ℚ ℂ D.toModel.coefficients))
           (G := D.toModel.model)
       IsMonHom D.toModel.genericIso.hom) := by
  have : Smooth A.toOver.hom := inferInstanceAs (Smooth A.variety.structureMap)
  exact AlgebraicGeometry.PELModuli.IntegralModel.EmbeddedGroupParameters.Coefficients.smooth_projective_group_coefficient_model ℚ ℂ A.toOver _
    (abelianProjectiveEmbedding A)

end

/-! Multiplication of two open subschemes of a smooth group is smooth,
so its scheme-theoretic image is open. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

def groupRightShear {S : Scheme} (G : Over S) [GrpObj G] : G ⊗ G ≅ G ⊗ G where
  hom := lift (fst G G * snd G G) (snd G G)
  inv := lift (fst G G / snd G G) (snd G G)
  hom_inv_id := by
    apply hom_ext <;> simp [GrpObj.comp_div]
  inv_hom_id := by
    apply hom_ext <;> simp [MonObj.comp_mul]

theorem group_multiplication_smooth {S : Scheme} (G : Over S) [GrpObj G] [Smooth G.hom] :
    Smooth (MonObj.mul (X := G)).left := by
  let e := groupRightShear G
  have : IsIso e.hom.left := ((Over.forget S).mapIso e).isIso_hom
  have h : e.hom ≫ fst G G = MonObj.mul := by
    simp only [e, groupRightShear, lift_fst, MonObj.mul_eq_mul]
  have hs : Smooth (e.hom.left ≫ (fst G G).left) :=
    inferInstanceAs (Smooth (e.hom.left ≫ pullback.fst G.hom G.hom))
  exact (congrArg (fun f : G ⊗ G ⟶ G => Smooth f.left) h) ▸ hs

def groupOpenProduct {S : Scheme} {V G : Over S} [GrpObj G] (i : V ⟶ G) : V ⊗ V ⟶ G :=
  (i ⊗ₘ i) ≫ MonObj.mul

theorem groupOpenProduct_points {S : Scheme} {V G T : Over S} [GrpObj G]
    (i : V ⟶ G) (a b : T ⟶ V) :
    lift a b ≫ groupOpenProduct i = (a ≫ i) * (b ≫ i) := by
  change lift a b ≫ (i ⊗ₘ i) ≫ MonObj.mul = _
  rw [← Category.assoc, lift_map]
  rfl

theorem groupOpenProduct_eq {S : Scheme} {V G : Over S} [GrpObj G] (i : V ⟶ G) :
    groupOpenProduct i = (fst V V ≫ i) * (snd V V ≫ i) := by
  simpa only [lift_fst_snd, Category.id_comp] using groupOpenProduct_points i (fst V V) (snd V V)

theorem groupOpenProduct_pullback {S T : Scheme} (f : T ⟶ S)
    {V G : Over S} [GrpObj G] (i : V ⟶ G) :
    (Over.pullback f).map (groupOpenProduct i) =
      (prodComparisonIso (Over.pullback f) V V).hom ≫ groupOpenProduct ((Over.pullback f).map i) := by
  rw [groupOpenProduct_eq, Functor.map_mul, groupOpenProduct_eq, MonObj.comp_mul]
  simp only [Functor.map_comp, ← Category.assoc, prodComparisonIso_hom,
    CartesianMonoidalCategory.prodComparison_fst, CartesianMonoidalCategory.prodComparison_snd]

theorem groupOpenProduct_smooth {S : Scheme} {V G : Over S} [GrpObj G] [Smooth G.hom]
    (i : V ⟶ G) [IsOpenImmersion i.left] : Smooth (groupOpenProduct i).left := by
  have : Smooth (MonObj.mul (X := G)).left := group_multiplication_smooth G
  have : IsOpenImmersion (i ⊗ₘ i).left := by
    change IsOpenImmersion (pullback.map _ _ _ _ i.left i.left (𝟙 S)
      ((Category.comp_id _).trans i.w.symm) ((Category.comp_id _).trans i.w.symm))
    infer_instance
  exact inferInstanceAs (Smooth ((i ⊗ₘ i).left ≫ (MonObj.mul (X := G)).left))

end

end OAI.ArithmeticGeometry.Descent.CMVariety.EmbeddedGroupCoefficients.Abelian
