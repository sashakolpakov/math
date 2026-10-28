import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.SymmetryAtPoint
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.SymmetryFormulaFibers
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.ContractionIntertwining
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FramedInducingFormula

/-! # Inducing Fiber Contraction Symmetry -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.InducingFiberContractionSymmetry

noncomputable section

/-! The actual inducing product respects symmetry between two test points when their Poincare frames correspond. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.LinePullback
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.BilinearPullback OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Contraction

theorem changed_sources {C : Type*} [Category C] {A B D E F G : C}
    (r : A ≅ B) (r' : D ≅ E) (e : A ≅ F) (e' : D ≅ G)
    (a : A ≅ D) (b : B ≅ E) (c : F ≅ G)
    (hr : a ≪≫ r' = r ≪≫ b) (he : e ≪≫ c = a ≪≫ e') :
    (r.symm ≪≫ e) ≪≫ c = b ≪≫ (r'.symm ≪≫ e') := by
  have h := Line.SymmetryFibers.inverse_square r r' a b hr.symm
  rw [Iso.trans_assoc, he, ← Iso.trans_assoc, h, Iso.trans_assoc]

theorem represented_intertwining {X : Scheme.{u}} {M N P M' N' P' : X.Modules}
    (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P) (γ : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M' N' P')
    (e : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N ≅ P) (e' : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M' N' ≅ P')
    (a : M ≅ M') (b : N ≅ N') (c : P ≅ P')
    (hβ : β = AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N P e.hom) (hγ : γ = AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M' N' P' e'.hom)
    (he : e ≪≫ c = AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr a b ≪≫ e') :
    Bilinear.BilinearPullback.toHom β ≫ c.hom = (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr a b).hom ≫ Bilinear.BilinearPullback.toHom γ := by
  rw [hβ, hγ]
  simpa only [Bilinear.BilinearPullback.toHom, Equiv.symm_apply_apply, Iso.trans_hom] using congrArg Iso.hom he

variable {S : Scheme.{u}} {E : Over S} (M N P : Line.Bundles.LineBundle E.left)
  (g : E ⟶ E) (e : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M.sheaf N.sheaf ≅ P.sheaf)
  (a : (Scheme.Modules.pullback g.left).obj M.sheaf ≅ M.sheaf)
  (b : (Scheme.Modules.pullback g.left).obj N.sheaf ≅ N.sheaf)
  (c : (Scheme.Modules.pullback g.left).obj P.sheaf ≅ P.sheaf)
  (he : (Scheme.Modules.pullback g.left).mapIso e ≪≫ c =
    (Tensor.LinePullback.pullbackIso g.left M.sheaf N.sheaf M.isLine N.isLine ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr a b) ≪≫ e)

include he

/-- Both restricted bilinear isomorphisms intertwine the individual actual fiber symmetries. -/
theorem formula_atPoint {T : Over S} (q : T ⟶ E) :
    RestrictedBilinearEquivariance.formula (q ≫ g) M N P e ≪≫ Line.SymmetryFibers.atPoint P g c q =
      AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr (Line.SymmetryFibers.atPoint M g a q) (Line.SymmetryFibers.atPoint N g b q) ≪≫
        RestrictedBilinearEquivariance.formula q M N P e := by
  have ht := Tensor.SymmetryAtPoint.atPoint M N g a b q
  have hf := Line.SymmetryFormulaFibers.atPoint (Tensor.LineBundles.tensor M N) P g e
    (Tensor.LinePullback.pullbackIso g.left M.sheaf N.sheaf M.isLine N.isLine ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr a b) c he q
  exact changed_sources (Tensor.LinePullback.pullbackIso (q ≫ g).left M.sheaf N.sheaf M.isLine N.isLine)
    (Tensor.LinePullback.pullbackIso q.left M.sheaf N.sheaf M.isLine N.isLine)
    ((Scheme.Modules.pullback (q ≫ g).left).mapIso e) ((Scheme.Modules.pullback q.left).mapIso e)
    (Line.SymmetryFibers.atPoint (Tensor.LineBundles.tensor M N) g
      (Tensor.LinePullback.pullbackIso g.left M.sheaf N.sheaf M.isLine N.isLine ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr a b) q)
    (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr (Line.SymmetryFibers.atPoint M g a q) (Line.SymmetryFibers.atPoint N g b q))
    (Line.SymmetryFibers.atPoint P g c q) ht hf

/-- Insert matching actual frames at qg and q to obtain the corresponding product-map equality. -/
theorem contraction_atPoint {T : Over S} (q : T ⟶ E)
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Line.Fibers.fiber M (q ≫ g)) (s' : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Line.Fibers.fiber M q)
    (hs : s ≪≫ Line.SymmetryFibers.atPoint M g a q = s') :
    Bilinear.Contraction.contractLeft (Bilinear.BilinearPullback.pullback (q ≫ g).left M.isLine N.isLine (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ _ e.hom)) s.hom ≫
        (Line.SymmetryFibers.atPoint P g c q).hom =
      (Line.SymmetryFibers.atPoint N g b q).hom ≫
        Bilinear.Contraction.contractLeft (Bilinear.BilinearPullback.pullback q.left M.isLine N.isLine (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ _ e.hom)) s'.hom := by
  have hβ := FramedInducingFormula.pullback_formula (q ≫ g) M N P e
  have hγ := FramedInducingFormula.pullback_formula q M N P e
  have hmap : Bilinear.BilinearPullback.toHom (Bilinear.BilinearPullback.pullback (q ≫ g).left M.isLine N.isLine (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ _ e.hom)) ≫
      (Line.SymmetryFibers.atPoint P g c q).hom =
    (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr (Line.SymmetryFibers.atPoint M g a q) (Line.SymmetryFibers.atPoint N g b q)).hom ≫
      Bilinear.BilinearPullback.toHom (Bilinear.BilinearPullback.pullback q.left M.isLine N.isLine (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ _ e.hom)) :=
    represented_intertwining _ _ (RestrictedBilinearEquivariance.formula (q ≫ g) M N P e)
      (RestrictedBilinearEquivariance.formula q M N P e)
      (Line.SymmetryFibers.atPoint M g a q) (Line.SymmetryFibers.atPoint N g b q)
      (Line.SymmetryFibers.atPoint P g c q) hβ hγ (formula_atPoint M N P g e a b c he q)
  exact Bilinear.ContractionIntertwining.contraction _ _
    (Line.SymmetryFibers.atPoint M g a q) (Line.SymmetryFibers.atPoint N g b q)
    (Line.SymmetryFibers.atPoint P g c q) hmap s.hom s'.hom (congrArg Iso.hom hs)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.InducingFiberContractionSymmetry
