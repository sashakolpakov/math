import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductEndomorphisms
import OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry
import OAI.AlgebraicGeometry.PELModuli.CMPoints.AbelianProducts
import OAI.AlgebraicGeometry.Albanese.Construction.SegreClosed

/-! # Product Comparison Model -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductComparisonModel.CM

noncomputable section

/-! The product of the actual number-field and good-reduction models,
with a constructed generic-fiber comparison and extending axis maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj
open OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductEndomorphisms.CM

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model K q jq)

local notation "bi" => OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (algebraMap ℤ_[q] ℚ_[q])
local notation "bg" => OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq

local instance integralGroup : GrpObj ((Over.pullback bi).obj A.integral.scheme) :=
  Functor.grpObjObj (F := Over.pullback bi)
local instance integralComm : IsCommMonObj ((Over.pullback bi).obj A.integral.scheme) :=
  Functor.isCommMonObj_obj (F := Over.pullback bi)

local instance integralProductGroup : GrpObj ((Over.pullback bi).obj (A.integral.scheme ⊗ A.integral.scheme)) :=
  Functor.grpObjObj (F := Over.pullback bi)
local instance integralProductComm : IsCommMonObj ((Over.pullback bi).obj (A.integral.scheme ⊗ A.integral.scheme)) :=
  Functor.isCommMonObj_obj (F := Over.pullback bi)

local instance genericGroup : GrpObj ((Over.pullback bg).obj A.variety.scheme) :=
  Functor.grpObjObj (F := Over.pullback bg)
local instance genericComm : IsCommMonObj ((Over.pullback bg).obj A.variety.scheme) :=
  Functor.isCommMonObj_obj (F := Over.pullback bg)

local instance genericProductGroup : GrpObj ((Over.pullback bg).obj (A.variety.scheme ⊗ A.variety.scheme)) :=
  Functor.grpObjObj (F := Over.pullback bg)
local instance genericProductComm : IsCommMonObj ((Over.pullback bg).obj (A.variety.scheme ⊗ A.variety.scheme)) :=
  Functor.isCommMonObj_obj (F := Over.pullback bg)

def factorIso : (Over.pullback bi).obj A.integral.scheme ≅
    (Over.pullback bg).obj A.variety.scheme := A.genericIso

local instance factorIso_group : IsMonHom (factorIso A).hom := A.genericIso_group

def genericIso :
    ((PELModuli.CMPoints.AbelianProducts.abelianProduct A.integral A.integral).pullback bi).scheme ≅
      ((PELModuli.CMPoints.AbelianProducts.abelianProduct A.variety A.variety).pullback bg).scheme :=
  ProductEndomorphisms.CM.productBaseChange A.integral.scheme bi ≪≫
    (factorIso A ⊗ᵢ factorIso A) ≪≫ (ProductEndomorphisms.CM.productBaseChange A.variety.scheme bg).symm

theorem genericIso_group : IsMonHom (CM.genericIso A).hom := by
  let : IsMonHom (ProductEndomorphisms.CM.productBaseChange A.integral.scheme bi).hom :=
    ProductEndomorphisms.CM.productBaseChange_group A.integral.scheme bi
  let : IsMonHom (ProductEndomorphisms.CM.productBaseChange A.variety.scheme bg).hom :=
    ProductEndomorphisms.CM.productBaseChange_group A.variety.scheme bg
  let : IsMonHom (ProductEndomorphisms.CM.productBaseChange A.variety.scheme bg).inv := by infer_instance
  exact inferInstanceAs (IsMonHom
    ((ProductEndomorphisms.CM.productBaseChange A.integral.scheme bi).hom ≫
      ((factorIso A).hom ⊗ₘ (factorIso A).hom) ≫ (ProductEndomorphisms.CM.productBaseChange A.variety.scheme bg).inv))

def productModel : NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model K q jq where
  dimension := A.dimension + A.dimension
  variety := PELModuli.CMPoints.AbelianProducts.abelianProduct A.variety A.variety
  integral := PELModuli.CMPoints.AbelianProducts.abelianProduct A.integral A.integral
  genericIso := CM.genericIso A
  genericIso_group := CM.genericIso_group A

theorem left_compatible :
    (Over.pullback bi).map (ProductEndomorphisms.CM.left A.integral.scheme) ≫ (CM.genericIso A).hom =
      (CM.genericIso A).hom ≫ (Over.pullback bg).map (ProductEndomorphisms.CM.left A.variety.scheme) := by
  have hi := ProductEndomorphisms.CM.left_baseChange A.integral.scheme bi
  have he := ProductEndomorphisms.CM.left_iso ((Over.pullback bi).obj A.integral.scheme) (factorIso A)
  have hg := ProductEndomorphisms.CM.left_baseChange A.variety.scheme bg
  have hg' : ProductEndomorphisms.CM.left ((Over.pullback bg).obj A.variety.scheme) ≫
      (ProductEndomorphisms.CM.productBaseChange A.variety.scheme bg).inv =
    (ProductEndomorphisms.CM.productBaseChange A.variety.scheme bg).inv ≫ (Over.pullback bg).map (ProductEndomorphisms.CM.left A.variety.scheme) := by
    apply (cancel_epi (ProductEndomorphisms.CM.productBaseChange A.variety.scheme bg).hom).mp
    rw [← Category.assoc, ← hg, Category.assoc,
      (ProductEndomorphisms.CM.productBaseChange A.variety.scheme bg).hom_inv_id, Category.comp_id,
      (ProductEndomorphisms.CM.productBaseChange A.variety.scheme bg).hom_inv_id_assoc]
  change _ ≫ (ProductEndomorphisms.CM.productBaseChange A.integral.scheme bi).hom ≫
    ((factorIso A).hom ⊗ₘ (factorIso A).hom) ≫ (ProductEndomorphisms.CM.productBaseChange A.variety.scheme bg).inv = _
  rw [← Category.assoc, hi, Category.assoc, ← Category.assoc
    (ProductEndomorphisms.CM.left ((Over.pullback bi).obj A.integral.scheme)), he, Category.assoc, hg']
  change (ProductEndomorphisms.CM.productBaseChange A.integral.scheme bi).hom ≫
    ((factorIso A).hom ⊗ₘ (factorIso A).hom) ≫ (ProductEndomorphisms.CM.productBaseChange A.variety.scheme bg).inv ≫
      (Over.pullback bg).map (ProductEndomorphisms.CM.left A.variety.scheme) =
    ((ProductEndomorphisms.CM.productBaseChange A.integral.scheme bi).hom ≫
      ((factorIso A).hom ⊗ₘ (factorIso A).hom) ≫ (ProductEndomorphisms.CM.productBaseChange A.variety.scheme bg).inv) ≫
      (Over.pullback bg).map (ProductEndomorphisms.CM.left A.variety.scheme)
  simp only [Category.assoc]

theorem right_compatible :
    (Over.pullback bi).map (ProductEndomorphisms.CM.right A.integral.scheme) ≫ (CM.genericIso A).hom =
      (CM.genericIso A).hom ≫ (Over.pullback bg).map (ProductEndomorphisms.CM.right A.variety.scheme) := by
  have hi := ProductEndomorphisms.CM.right_baseChange A.integral.scheme bi
  have he := ProductEndomorphisms.CM.right_iso ((Over.pullback bi).obj A.integral.scheme) (factorIso A)
  have hg := ProductEndomorphisms.CM.right_baseChange A.variety.scheme bg
  have hg' : ProductEndomorphisms.CM.right ((Over.pullback bg).obj A.variety.scheme) ≫
      (ProductEndomorphisms.CM.productBaseChange A.variety.scheme bg).inv =
    (ProductEndomorphisms.CM.productBaseChange A.variety.scheme bg).inv ≫ (Over.pullback bg).map (ProductEndomorphisms.CM.right A.variety.scheme) := by
    apply (cancel_epi (ProductEndomorphisms.CM.productBaseChange A.variety.scheme bg).hom).mp
    rw [← Category.assoc, ← hg, Category.assoc,
      (ProductEndomorphisms.CM.productBaseChange A.variety.scheme bg).hom_inv_id, Category.comp_id,
      (ProductEndomorphisms.CM.productBaseChange A.variety.scheme bg).hom_inv_id_assoc]
  change _ ≫ (ProductEndomorphisms.CM.productBaseChange A.integral.scheme bi).hom ≫
    ((factorIso A).hom ⊗ₘ (factorIso A).hom) ≫ (ProductEndomorphisms.CM.productBaseChange A.variety.scheme bg).inv = _
  rw [← Category.assoc, hi, Category.assoc, ← Category.assoc
    (ProductEndomorphisms.CM.right ((Over.pullback bi).obj A.integral.scheme)), he, Category.assoc, hg']
  change (ProductEndomorphisms.CM.productBaseChange A.integral.scheme bi).hom ≫
    ((factorIso A).hom ⊗ₘ (factorIso A).hom) ≫ (ProductEndomorphisms.CM.productBaseChange A.variety.scheme bg).inv ≫
      (Over.pullback bg).map (ProductEndomorphisms.CM.right A.variety.scheme) =
    ((ProductEndomorphisms.CM.productBaseChange A.integral.scheme bi).hom ≫
      ((factorIso A).hom ⊗ₘ (factorIso A).hom) ≫ (ProductEndomorphisms.CM.productBaseChange A.variety.scheme bg).inv) ≫
      (Over.pullback bg).map (ProductEndomorphisms.CM.right A.variety.scheme)
  simp only [Category.assoc]

def leftRing {S : Scheme} (G : Over S) [GrpObj G] [IsCommMonObj G] :
    FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd (G ⊗ G) := Additive.ofMul (Grp.ofHom (ProductEndomorphisms.CM.left G))

def rightRing {S : Scheme} (G : Over S) [GrpObj G] [IsCommMonObj G] :
    FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd (G ⊗ G) := Additive.ofMul (Grp.ofHom (ProductEndomorphisms.CM.right G))

def leftAlgebraic {S : Scheme} {g : ℕ} (G : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) :
    FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd (PELModuli.CMPoints.AbelianProducts.abelianProduct G G).scheme := leftRing G.scheme

def rightAlgebraic {S : Scheme} {g : ℕ} (G : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) :
    FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd (PELModuli.CMPoints.AbelianProducts.abelianProduct G G).scheme := rightRing G.scheme

def leftEnd : (productModel A).ExtendingEndomorphism where
  generic := leftAlgebraic A.variety
  integral := leftAlgebraic A.integral
  compatible := left_compatible A

def rightEnd : (productModel A).ExtendingEndomorphism where
  generic := rightAlgebraic A.variety
  integral := rightAlgebraic A.integral
  compatible := right_compatible A

def complexProductIso (j : K →+* ℂ) :
    ((productModel A).complexFiber j).scheme ≅
      (A.complexFiber j).scheme ⊗ (A.complexFiber j).scheme :=
  ProductEndomorphisms.CM.productBaseChange A.variety.scheme (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap j)

def productProjectivePresentation (j : K →+* ℂ)
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber j).scheme.left (A.complexFiber j).scheme.hom) :
    Foundations.Scheme.SmoothProjective.ProjectivePresentation ((productModel A).complexFiber j).scheme.left
      ((productModel A).complexFiber j).scheme.hom where
  ambientDimension := (Albanese.Construction.SegreClosed.tensorProjectivePresentation _ _ P P).ambientDimension
  embedding := (complexProductIso A j).hom.left ≫ (Albanese.Construction.SegreClosed.tensorProjectivePresentation _ _ P P).embedding
  closedImmersion := by
    let : IsIso (complexProductIso A j).hom.left :=
      inferInstanceAs (IsIso ((Over.forget Foundations.Scheme.ProjectiveSpace.complexBase).map (complexProductIso A j).hom))
    infer_instance
  over_base := by
    rw [Category.assoc, (Albanese.Construction.SegreClosed.tensorProjectivePresentation _ _ P P).over_base]
    exact (complexProductIso A j).hom.w

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductComparisonModel.CM
