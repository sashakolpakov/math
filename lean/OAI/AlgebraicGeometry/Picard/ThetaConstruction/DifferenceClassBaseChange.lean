import OAI.AlgebraicGeometry.Picard.ThetaConstruction.DifferenceTrivialityHomogeneity
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeNormalizationFibers
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeCubeClasses
import OAI.RepresentationTheory.Theta.Geometric.TestDifferenceClasses

/-! # Difference Class Base Change -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.DifferenceClassBaseChange.Geometric

noncomputable section

/-! The normalized difference bundle evaluates on pairs of actual
scheme points by the original Picard group formula. That formula
commutes with base change and vanishes for homogeneous field lines. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.RepresentationTheory.Theta.Geometric.TestDifferenceClasses

variable {S : Scheme.{0}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)

theorem relativeDifference_pair_class {U : Over S} (a b : U ⟶ A.scheme) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf ((RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L).pullback (lift a b).left) =
      RepresentationTheory.Theta.Geometric.TestDifferenceClasses.groupDifferenceClass A.scheme (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (RelativeDifferenceBundle.Geometric.identityNormalizedLine A L)) a b := by
  have h := RepresentationTheory.Theta.Geometric.Picard.PicardPullback.algebraicDifferenceBundle_pullback_class (RelativeDifferenceBundle.Geometric.identityNormalizedLine A L)
    (fst A.scheme A.scheme).left (snd A.scheme A.scheme).left μ[A.scheme].left (lift a b).left
  have h₁ : (lift a b).left ≫ (fst A.scheme A.scheme).left = a.left :=
    congrArg Over.Hom.left (lift_fst a b)
  have h₂ : (lift a b).left ≫ (snd A.scheme A.scheme).left = b.left :=
    congrArg Over.Hom.left (lift_snd a b)
  have hm : (lift a b).left ≫ μ[A.scheme].left = (a * b).left := rfl
  rw [h₁, h₂, hm] at h
  exact h

private theorem originalDifference_formula {S : Scheme.{0}}
    (X : Over S) [GrpObj X] (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass X.left)
    {U : Over S} (a b : U ⟶ X) :
    RepresentationTheory.Theta.Geometric.TestDifferenceClasses.groupDifferenceClass X q a b =
      RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (a * b).left q * (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback a.left q)⁻¹ *
        (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback b.left q)⁻¹ := by
  have h57 (r : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass U.left) : Homomorphisms.LineBundleDual.Construction.dualLineBundleClass r = r⁻¹ :=
    eq_inv_of_mul_eq_one_left (Homomorphisms.LineBundleEvaluation.Construction.tensorClass_dual r)
  dsimp only [RepresentationTheory.Theta.Geometric.TestDifferenceClasses.groupDifferenceClass]
  exact congrArg₂ (fun x y : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass U.left => RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (a * b).left q * x * y)
    (h57 (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback a.left q)) (h57 (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback b.left q))

private theorem pullback_groupDifferenceClass {S : Scheme.{0}}
    (X : Over S) [GrpObj X] (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass X.left)
    {S' : Scheme.{0}} (f : S' ⟶ S) {U : Over S} (a b : U ⟶ X) :
    letI : GrpObj ((Over.pullback f).obj X) := Functor.grpObjObj
    RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (pullback.fst U.hom f) (RepresentationTheory.Theta.Geometric.TestDifferenceClasses.groupDifferenceClass X q a b) =
      RepresentationTheory.Theta.Geometric.TestDifferenceClasses.groupDifferenceClass ((Over.pullback f).obj X)
        (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (pullback.fst X.hom f) q)
        ((Over.pullback f).map a) ((Over.pullback f).map b) := by
  let : GrpObj ((Over.pullback f).obj X) := Functor.grpObjObj
  let p := RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (pullback.fst U.hom f)
  have hformula := p.map_mul
    (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (a * b).left q * (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback a.left q)⁻¹)
    ((RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback b.left q)⁻¹)
  have hfirst := p.map_mul (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (a * b).left q) ((RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback a.left q)⁻¹)
  have ha := (p.map_inv (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback a.left q)).trans
    (congrArg Inv.inv (RelativeCubeClasses.Geometric.pointClass_baseChange q f a))
  have hb := (p.map_inv (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback b.left q)).trans
    (congrArg Inv.inv (RelativeCubeClasses.Geometric.pointClass_baseChange q f b))
  have hmul : (Over.pullback f).map (a * b) =
      (Over.pullback f).map a * (Over.pullback f).map b := (Over.pullback f).map_mul a b
  have hab := (RelativeCubeClasses.Geometric.pointClass_baseChange q f (a * b)).trans
    (congrArg (fun v : (Over.pullback f).obj U ⟶ (Over.pullback f).obj X =>
      RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback v.left (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (pullback.fst X.hom f) q)) hmul)
  have hsource := congrArg p (originalDifference_formula X q a b)
  have htarget := originalDifference_formula ((Over.pullback f).obj X)
    (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (pullback.fst X.hom f) q)
    ((Over.pullback f).map a) ((Over.pullback f).map b)
  exact hsource.trans ((hformula.trans (congrArg₂ (· * ·)
    (hfirst.trans (congrArg₂ (· * ·) hab ha)) hb)).trans htarget.symm)

theorem groupDifferenceClass_baseChange (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass A.scheme.left)
    {S' : Scheme.{0}} (f : S' ⟶ S) {U : Over S} (a b : U ⟶ A.scheme) :
    RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (pullback.fst U.hom f) (RepresentationTheory.Theta.Geometric.TestDifferenceClasses.groupDifferenceClass A.scheme q a b) =
      RepresentationTheory.Theta.Geometric.TestDifferenceClasses.groupDifferenceClass (A.pullback f).scheme
        (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (pullback.fst A.scheme.hom f) q)
        ((Over.pullback f).map a) ((Over.pullback f).map b) := by
  exact pullback_groupDifferenceClass A.scheme q f a b

variable {k : Type} [Field k] (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
    (M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.scheme.left)

theorem identityNormalizedLine_class_overField :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (RelativeDifferenceBundle.Geometric.identityNormalizedLine B M) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M := by
  have h := RelativeNormalizationFibers.Geometric.identityNormalizedLine_fieldPullback_class B M (𝟙 B.scheme.left)
    B.scheme.hom (𝟙 (Spec (.of k))) ((Category.id_comp _).trans (Category.comp_id _).symm)
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 B.scheme.left) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (RelativeDifferenceBundle.Geometric.identityNormalizedLine B M)) =
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 B.scheme.left) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M) at h
  simpa only [AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id] using h

theorem homogeneousLine_groupDifference (hM : AbelianModuli.ReferenceFamily.HomogeneousLinePowers.IsHomogeneousLineClass B (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M))
    {U : Over (Spec (.of k))} (a b : U ⟶ B.scheme) :
    RepresentationTheory.Theta.Geometric.TestDifferenceClasses.groupDifferenceClass B.scheme (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M) a b = 1 := by
  obtain ⟨e⟩ := (DifferenceTrivialityHomogeneity.Geometric.difference_trivial_iff_homogeneous_line B M).mpr hM
  have hc : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf ((RelativeDifferenceBundle.Geometric.relativeDifferenceBundle B M).pullback (lift a b).left) = 1 :=
    Quotient.sound ⟨(Scheme.Modules.pullback (lift a b).left).mapIso e ≪≫
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (lift a b).left⟩
  rw [relativeDifference_pair_class, identityNormalizedLine_class_overField] at hc
  exact hc

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.DifferenceClassBaseChange.Geometric
