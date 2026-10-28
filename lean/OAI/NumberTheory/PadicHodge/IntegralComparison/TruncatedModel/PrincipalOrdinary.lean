import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.OrdinarySectionMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFractionClass
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalCoefficientComponent

/-! # Principal Ordinary -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalOrdinary.OrdinaryComparison

noncomputable section

/-! The actual principal comparison is the ordinary affine comparison
preceded by the canonical principal PD-to-ordinary isomorphism. -/
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

def map : PrincipalFractionClass.target p k n X U ⟶
    ((Principal.Comparison.restriction p k n X U).mapHomologicalComplex
      (.up ℕ)).obj
      (((SectionBifunctor.sections p k n X Y f).mapHomologicalComplex
        (.up ℕ)).obj I.cocomplex) :=
  (GeometricComparison.ComplexAssemblyPresheaves.ComplexAssemblyCoefficients.iso (Principal.Comparison.coefficients p k)
    ((AffinePrincipal.Diagram.functor X.left U.val U.property).op ⋙
      OrdinaryBaseIso.Ordinary.target p k n X)).inv ≫
    (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyTrans.ComplexAssemblyTransport.iso
      (AffinePrincipal.Diagram.functor X.left U.val U.property).op
      (𝟭 _) (.up ℕ) (OrdinarySectionMap.Ordinary.rawDiagram p k n X)).inv ≫
    ((Principal.Comparison.restriction p k n X U).mapHomologicalComplex
      (.up ℕ)).map (OrdinarySectionMap.Ordinary.map p k n X Y f hp I)

theorem component (q : ℕ) (r : PrincipalFrame.Index X.left U) :
    ((OrdinaryComparison.map p k n X Y f hp U I).f q).app (op r) =
      (Principal.Comparison.coefficients p k).map
        (((OrdinaryBaseIso.Ordinary.pdIso p k n X Y f hp).inv.app
          (op ((AffinePrincipal.Diagram.functor X.left U.val U.property).obj r))).f q) ≫
      ((FrameInjective.Comparison.map p k n X Y f hp I).f q).app
        (op ((AffinePrincipal.Diagram.functor X.left U.val U.property).obj r)) := by
  change 𝟙 _ ≫ 𝟙 _ ≫ (_ ≫ _) = _
  simp only [Category.id_comp]
  rfl

theorem comparison :
    (PrincipalFractionClass.iso p k n X Y f hp U).hom ≫
        OrdinaryComparison.map p k n X Y f hp U I =
      Principal.Comparison.map p k n X Y f hp U I := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply NatTrans.ext
  funext r
  rw [comp_f, NatTrans.comp_app, component]
  let L := Principal.Comparison.coefficients p k
  let a := ((Principal.Comparison.nativePDMap p k n X Y f hp U).f q).app r
  let e := ((OrdinaryBaseIso.Ordinary.pdIso p k n X Y f hp).app
    ((AffinePrincipal.Diagram.functor X.left U.val U.property).op.obj r))
  let b := ((FrameInjective.Comparison.map p k n X Y f hp I).f q).app
    ((AffinePrincipal.Diagram.functor X.left U.val U.property).op.obj r)
  change L.map (a ≫ e.hom.f q) ≫ (L.map (e.inv.f q) ≫ b) =
    (L.map a ≫ 𝟙 _) ≫ 𝟙 _ ≫ b
  have he : e.hom.f q ≫ e.inv.f q = 𝟙 _ := by
    simpa only [comp_f, id_f] using congrArg (fun z => z.f q) e.hom_inv_id
  have h := congrArg (fun z => L.map a ≫ L.map z ≫ b) he
  simp only [L.map_comp, Category.assoc, Category.id_comp, Category.comp_id] at h ⊢
  convert h using 1; rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalOrdinary.OrdinaryComparison
