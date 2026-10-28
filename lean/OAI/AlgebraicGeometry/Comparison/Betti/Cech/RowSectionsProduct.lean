import OAI.AlgebraicGeometry.Comparison.Betti.FlasqueCechTotal
import OAI.AlgebraicGeometry.Comparison.Betti.Finite.ProductQuasiIso

/-! # Row Sections Product -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Cech.RowSectionsProduct

noncomputable section

/-! Each transposed Čech row is the actual product of section complexes on its tuple intersections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex₂

variable {X : TopCat.{0}} {ι : Type} (U : ι → Opens X)

abbrev additiveOpenSectionsFunctor (V : Opens X) : TopCat.Sheaf AddCommGrpCat.{0} X ⥤ AddCommGrpCat.{0} :=
  TopCat.Sheaf.forget AddCommGrpCat.{0} X ⋙
    (CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{0}).obj (op V)

instance additiveOpenSectionsFunctor_additive (V : Opens X) :
    (additiveOpenSectionsFunctor V).Additive where
  map_add := rfl

variable (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ) (p : ℕ)

def cechTupleSectionsComplex (t : Fin (p + 1) → ι) : CochainComplex AddCommGrpCat.{0} ℕ :=
  ((additiveOpenSectionsFunctor (∏ᶜ fun k : Fin (p + 1) => U (t k))).mapHomologicalComplex (.up ℕ)).obj K

def cechRowSectionProjection (t : Fin (p + 1) → ι) :
    (FlasqueCechTotal.additiveSheafSectionCechBicomplex U K).flip.X p ⟶ cechTupleSectionsComplex U K p t where
  f n := CategoryTheory.Limits.Pi.π
    (fun s : Fin (p + 1) → ι => (K.X n).obj.obj (op (∏ᶜ fun k => U (s k)))) t
  comm' n m _ := by
    exact (CategoryTheory.Limits.Pi.map_π
      (fun s : Fin (p + 1) → ι => (K.d n m).hom.app (op (∏ᶜ fun k => U (s k)))) t).symm

def cechRowSectionsFan : Fan (cechTupleSectionsComplex U K p) :=
  Fan.mk ((FlasqueCechTotal.additiveSheafSectionCechBicomplex U K).flip.X p) (cechRowSectionProjection U K p)

def cechRowSectionsFan_isLimit : IsLimit (cechRowSectionsFan U K p) := by
  apply HomologicalComplex.isLimitOfEval
  intro n
  exact (isLimitMapConeFanMkEquiv (HomologicalComplex.eval AddCommGrpCat (.up ℕ) n)
    (cechTupleSectionsComplex U K p) (cechRowSectionProjection U K p)).symm
      (productIsProduct (fun t : Fin (p + 1) → ι =>
        (K.X n).obj.obj (op (∏ᶜ fun k => U (t k)))))

def cechRowSectionsProductIso :
    (FlasqueCechTotal.additiveSheafSectionCechBicomplex U K).flip.X p ≅ ∏ᶜ cechTupleSectionsComplex U K p :=
  (cechRowSectionsFan_isLimit U K p).conePointUniqueUpToIso (productIsProduct _)

theorem cechRowSectionsProductIso_hom_π (t : Fin (p + 1) → ι) :
    (cechRowSectionsProductIso U K p).hom ≫
      CategoryTheory.Limits.Pi.π (cechTupleSectionsComplex U K p) t =
        cechRowSectionProjection U K p t :=
  (productIsProduct _).fac (cechRowSectionsFan U K p) (Discrete.mk t)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Cech.RowSectionsProduct
