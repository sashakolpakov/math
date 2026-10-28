import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.AffineSheaf
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalOrdinary
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FractionClass

/-! # Principal Sheaf -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSheaf.Comparison

noncomputable section

/-! Restricting the genuine sheaf comparison to the principal diagram
recovers the original local PD comparison in integral-form coordinates. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (U : X.left.affineOpens)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))

def restriction :
    Sheaf (Opens.grothendieckTopology X.left)
        (ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ⥤
      ((PrincipalFrame.Index X.left U)ᵒᵖ ⥤
        ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) :=
  sheafToPresheaf (Opens.grothendieckTopology X.left) _ ⋙
    GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback
      (Principal.DeRhamSectionUnit.opens (Truncated.Witt.Ring p k n) X U)

instance restriction_additive : (restriction p k n X U).Additive := by
  dsimp only [restriction]
  infer_instance

def map : FractionClass.Integral.target p k n X U ⟶
    ((Principal.Comparison.restriction p k n X U).mapHomologicalComplex
      (.up ℕ)).obj
      (((SectionBifunctor.sections p k n X Y f).mapHomologicalComplex
        (.up ℕ)).obj I.cocomplex) :=
  ((restriction p k n X U).mapHomologicalComplex (.up ℕ)).map
    (ModelSheafComparison.map p k n X Y f hp I)

theorem component (q : ℕ) (r : PrincipalFrame.Index X.left U) :
    ((Comparison.map p k n X Y f hp U I).f q).app (op r) =
      ((ModelSheafComparison.map p k n X Y f hp I).f q).hom.app
        (op ((AffinePrincipal.Diagram.functor X.left U.val U.property).obj r).val) := rfl

theorem raw_component (V : X.left.affineOpens) (q : ℕ) :
    (ModelSheafComparison.rawMap p k n X Y f hp I V).f q =
      (Principal.Comparison.coefficients p k).map
        (((OrdinaryBaseIso.Ordinary.pdIso p k n X Y f hp).inv.app (op V)).f q) ≫
      ((FrameInjective.Comparison.map p k n X Y f hp I).f q).app (op V) := by
  change 𝟙 _ ≫ (_ ≫ _) = _
  exact Category.id_comp _

variable (σ : Type) [LinearOrder σ]
  [Algebra (MvPolynomial σ (Truncated.Witt.Ring p k n))
    (IntrinsicDeRham.SectionUnit.Intrinsic.ring (Truncated.Witt.Ring p k n) X U.val)]
  [IsScalarTower (Truncated.Witt.Ring p k n) (MvPolynomial σ (Truncated.Witt.Ring p k n))
    (IntrinsicDeRham.SectionUnit.Intrinsic.ring (Truncated.Witt.Ring p k n) X U.val)]
  [Algebra.Etale (MvPolynomial σ (Truncated.Witt.Ring p k n))
    (IntrinsicDeRham.SectionUnit.Intrinsic.ring (Truncated.Witt.Ring p k n) X U.val)]

theorem unit_comparison :
    ((GeometricComparison.ComplexAssemblyPresheaves.ComplexAssemblyCoefficients.presheaves
      (Principal.Comparison.coefficients p k)).mapHomologicalComplex (.up ℕ)).map
        (PrincipalSheafIso.iso p k n X U σ).hom ≫
      Comparison.map p k n X Y f hp U I =
    PrincipalOrdinary.OrdinaryComparison.map p k n X Y f hp U I := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply NatTrans.ext
  funext r
  let V := (AffinePrincipal.Diagram.functor X.left U.val U.property).obj r.unop
  have h := AffineSheaf.Comparison.unit_affine p k n X Y f hp I V q
  rw [raw_component] at h
  rw [comp_f, NatTrans.comp_app, component,
    PrincipalOrdinary.OrdinaryComparison.component]
  change (OrdinarySectionMap.Ordinary.coefficients p k n).map
      ((IntrinsicDeRham.SectionUnit.Intrinsic.unit (Truncated.Witt.Ring p k n) X V.val).f q) ≫ _ = _
  exact h

theorem comparison :
    (FractionClass.Integral.iso p k n X Y f hp U σ).hom ≫
        Comparison.map p k n X Y f hp U I =
      Principal.Comparison.map p k n X Y f hp U I := by
  change ((PrincipalFractionClass.iso p k n X Y f hp U).hom ≫
    ((GeometricComparison.ComplexAssemblyPresheaves.ComplexAssemblyCoefficients.presheaves
      (Principal.Comparison.coefficients p k)).mapHomologicalComplex (.up ℕ)).map
      (PrincipalSheafIso.iso p k n X U σ).hom) ≫
      Comparison.map p k n X Y f hp U I = _
  rw [Category.assoc, unit_comparison p k n X Y f hp U I σ]
  exact PrincipalOrdinary.OrdinaryComparison.comparison p k n X Y f hp U I

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSheaf.Comparison
