import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.RefinedReindex
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ConeTotal

/-! # Functor Refinement Coordinates -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Section.FunctorRefinementCoordinates.SectionFunctorRefinementCoordinates

noncomputable section

/-! Reindexing a section functor before or after forming its
cochain complex uses the same original total-map components. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe a b c d e f g h v w
variable {A : Type a} [Category.{b} A] [Preadditive A]
  {B : Type c} [Category.{d} B] [Abelian B] [HasProducts.{0} B] [HasCoproducts.{0} B]
  {C : Type e} [Category.{f} C] [HasBinaryProducts C]
  {D : Type g} [Category.{h} D] [Quiver.IsThin D] [HasBinaryProducts D]
  {E : Type v} [Category.{w} E]
  (S : A ⥤ (Eᵒᵖ ⥤ B)) [S.Additive] (K : CochainComplex A ℕ)
  (G : C ⥤ D) (F : D ⥤ E) {ι κ : Type} (U : ι → C) (V : κ → D)
  [∀ (q : ℕ) (t : Fin (q + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) G]
  (r : FormalCoproduct.mk ι (G.obj ∘ U) ⟶ FormalCoproduct.mk κ V)

def oldSections := ((S ⋙ NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := B) F).mapHomologicalComplex (.up ℕ)).obj K
def newSections := ((S ⋙ NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := B) (G ⋙ F)).mapHomologicalComplex (.up ℕ)).obj K

def refinement : (CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex V (oldSections S K F)).total (.up ℕ) ⟶
    (CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex U (newSections S K G F)).total (.up ℕ) :=
  CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.map G U V r (oldSections S K F)

def bicomplex := CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.bicomplexMap G U V r (oldSections S K F)

theorem component (q : ℕ) : (refinement S K G F U V r).f q =
    (HomologicalComplex₂.total.map (bicomplex S K G F U V r) (.up ℕ)).f q := rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Section.FunctorRefinementCoordinates.SectionFunctorRefinementCoordinates
