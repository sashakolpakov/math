import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.Refinement
import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductBicomplex
import OAI.AlgebraicGeometry.Comparison.Betti.TotalExists

/-! # Refined Reindex -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.RefinedReindex.CechPresheafRefinedReindex

noncomputable section

/-! A projected refinement acts on the original Cech bicomplex of a
presheaf complex, naturally in the entire presheaf complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v s t a b
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {D : Type s} [Category.{t} D] [Quiver.IsThin D] [HasBinaryProducts D]
  {A : Type a} [Category.{b} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  (F : C ⥤ D) {ι κ : Type} (U : ι → C) (V : κ → D)
  [∀ (n : ℕ) (t : Fin (n + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) F]
  (r : FormalCoproduct.mk ι (F.obj ∘ U) ⟶ FormalCoproduct.mk κ V)

local notation "H" => OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := A) F

def transformation : IntegralComparison.NonemptyCechNerve.complexFunctor (A := A) V ⟶
    H ⋙ IntegralComparison.NonemptyCechNerve.complexFunctor (A := A) U :=
  NonemptyCech.Refinement.NonemptyCechRefinement.transformation V (F.obj ∘ U) r ≫
    (NonemptyCech.ProductBaseChangeNaturality.NonemptyCechProductBaseChangeNaturality.iso F U).inv

def source : CochainComplex (Dᵒᵖ ⥤ A) ℕ ⥤ HomologicalComplex₂ A (.up ℕ) (.up ℕ) :=
  (IntegralComparison.NonemptyCechNerve.complexFunctor V).mapHomologicalComplex (.up ℕ)

def target : CochainComplex (Dᵒᵖ ⥤ A) ℕ ⥤ HomologicalComplex₂ A (.up ℕ) (.up ℕ) :=
  (H ⋙ IntegralComparison.NonemptyCechNerve.complexFunctor U).mapHomologicalComplex (.up ℕ)

def bicomplexMap (K : CochainComplex (Dᵒᵖ ⥤ A) ℕ) : (source V).obj K ⟶ (target F U).obj K :=
  ((transformation F U V r).mapHomologicalComplex (.up ℕ)).app K

local instance hasTotal (K : HomologicalComplex₂ A (.up ℕ) (.up ℕ)) : K.HasTotal (.up ℕ) :=
  AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts K

def map (K : CochainComplex (Dᵒᵖ ⥤ A) ℕ) : ((source V).obj K).total (.up ℕ) ⟶
    ((target F U).obj K).total (.up ℕ) :=
  HomologicalComplex₂.total.map (bicomplexMap F U V r K) (.up ℕ)

omit [HasCoproducts.{0} A] in
theorem bicomplex_naturality {K L : CochainComplex (Dᵒᵖ ⥤ A) ℕ} (f : K ⟶ L) :
    (source V).map f ≫ bicomplexMap F U V r L = bicomplexMap F U V r K ≫ (target F U).map f :=
  ((transformation F U V r).mapHomologicalComplex (.up ℕ)).naturality f

theorem naturality {K L : CochainComplex (Dᵒᵖ ⥤ A) ℕ} (f : K ⟶ L) :
    HomologicalComplex₂.total.map ((source V).map f) (.up ℕ) ≫ CechPresheafRefinedReindex.map F U V r L =
      CechPresheafRefinedReindex.map F U V r K ≫ HomologicalComplex₂.total.map ((target F U).map f) (.up ℕ) := by
  let T := HomologicalComplex₂.totalFunctor A (.up ℕ) (.up ℕ) (.up ℕ)
  exact (T.map_comp _ _).symm.trans
    ((congrArg T.map (bicomplex_naturality F U V r f)).trans (T.map_comp _ _))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.RefinedReindex.CechPresheafRefinedReindex
