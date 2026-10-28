import OAI.AlgebraicGeometry.PELModuli.IntegralModel.SpreadingOutCapstones
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.OpenLocalization
import OAI.ArithmeticGeometry.Models.SpreadingOut.SplitComponentsBaseChange

/-! # Split Localized Models -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.SplitLocalizedModels

noncomputable section

/-! The completed SpreadingOut simultaneous model over IntegralModel's precise localized
arithmetic base. Split geometric components, designated abelian structures,
all diagram maps and generic comparisons are retained by actual base change. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

/-- Construct the full split arithmetic diagram over a localized ring of
integers with the specified level inverted. SpreadingOut model existence, geometric
component splitting and preservation of surjective arrows are conclusions. -/
theorem exists_split_localized_diagram_model
    {K : Type} [Field K] [NumberField K] (κ : K →+* ℂ)
    (D : ModelsHas.FiniteDiagram K) (N : ℕ) (hN : N ≠ 0) :
    ∃ B : Base.ArithmeticBaseExtension K κ, IsUnit (N : B.R) ∧ N ∣ B.denominator ∧
      ∃ (M : D.objects → Over B.base)
        (fM : ∀ a, M (D.src a) ⟶ M (D.dst a))
        (e : ∀ i, (Over.pullback B.generic).obj (M i) ≅
          (Over.pullback B.fieldExtension).obj (D.X i))
        (groupM : ∀ b, GrpObj (M (D.abelianIndex b))),
        (∀ i, Smooth (M i).hom ∧ IsProper (M i).hom ∧ ModelsHas.HasSplitGeometricComponents (M i)) ∧
        (∀ a, (Over.pullback B.generic).map (fM a) ≫ (e (D.dst a)).hom =
          (e (D.src a)).hom ≫ (Over.pullback B.fieldExtension).map (D.f a)) ∧
        (∀ b,
          letI := D.group b
          letI := groupM b
          letI : GrpObj ((Over.pullback B.generic).obj (M (D.abelianIndex b))) :=
            Functor.grpObjObj
          letI : GrpObj ((Over.pullback B.fieldExtension).obj (D.X (D.abelianIndex b))) :=
            Functor.grpObjObj
          IsCommMonObj (M (D.abelianIndex b)) ∧
            GeometricallyConnected (M (D.abelianIndex b)).hom ∧
            IsMonHom (e (D.abelianIndex b)).hom) ∧
        (∀ a, Surjective (D.f a).left → Surjective (fM a).left) := by
  obtain ⟨Q⟩ := SpreadingOutCapstones.provedSpreadingOutInput K D
  let seed : Base.ArithmeticBaseExtension K κ := {
    extension := Q.extension
    embedding := (Base.ArithmeticBaseExtension.ofFiniteExtension Q.extension κ 1 one_ne_zero).embedding
    embedding_extends :=
      (Base.ArithmeticBaseExtension.ofFiniteExtension Q.extension κ 1 one_ne_zero).embedding_extends
    denominator := 1
    denominator_ne_zero := one_ne_zero }
  obtain ⟨d, hd, hdiv, b, hb⟩ := seed.arithmetic_open_localization Q.base N hN
  let B := seed.withDenominator d hd
  let F := Over.pullback b
  let G := Over.pullback B.generic
  let H := Over.pullback Q.base.generic
  let c : F ⋙ G ≅ H := (Over.pullbackComp B.generic b).symm ≪≫
    eqToIso (congrArg (fun k => Over.pullback k) hb)
  let ec (i : D.objects) : G.obj (F.obj (Q.M i)) ≅ H.obj (Q.M i) := c.app (Q.M i)
  let groupN (j : D.abelians) : GrpObj (F.obj (Q.M (D.abelianIndex j))) := by
    let := Q.groupM j
    exact Functor.grpObjObj (F := F)
  refine ⟨B, B.divisor_isUnit N hdiv, hdiv, (fun i => F.obj (Q.M i)),
    (fun a => F.map (Q.fM a)), (fun i => ec i ≪≫ Q.e i), groupN, ?_, ?_, ?_, ?_⟩
  · intro i
    have := (Q.properties i).1
    have := (Q.properties i).2.1
    exact ⟨inferInstanceAs (Smooth (pullback.snd (Q.M i).hom b)),
      inferInstanceAs (IsProper (pullback.snd (Q.M i).hom b)),
      ArithmeticGeometry.Models.SpreadingOut.SplitComponentsBaseChange.Construction.hasSplitGeometricComponents_baseChange b (Q.M i) (Q.properties i).2.2⟩
  · intro a
    have hc : G.map (F.map (Q.fM a)) ≫ (ec (D.dst a)).hom =
        (ec (D.src a)).hom ≫ H.map (Q.fM a) := c.hom.naturality (Q.fM a)
    change G.map (F.map (Q.fM a)) ≫ (ec (D.dst a)).hom ≫ (Q.e (D.dst a)).hom =
      ((ec (D.src a)).hom ≫ (Q.e (D.src a)).hom) ≫
        (Over.pullback (Spec.map
          (CommRingCat.ofHom (algebraMap K Q.extension.carrier)))).map (D.f a)
    rw [← Category.assoc, hc, Category.assoc, Q.compatible, Category.assoc]
  · intro j
    let := D.group j
    let := Q.groupM j
    let : GrpObj (F.obj (Q.M (D.abelianIndex j))) := groupN j
    let : GrpObj (G.obj (F.obj (Q.M (D.abelianIndex j)))) := Functor.grpObjObj (F := G)
    let : GrpObj (H.obj (Q.M (D.abelianIndex j))) := Functor.grpObjObj (F := H)
    have : IsCommMonObj (Q.M (D.abelianIndex j)) := (Q.abelian j).1
    have : GeometricallyConnected (Q.M (D.abelianIndex j)).hom := (Q.abelian j).2.1
    refine ⟨inferInstanceAs (IsCommMonObj (F.obj (Q.M (D.abelianIndex j)))),
      inferInstanceAs (GeometricallyConnected (pullback.snd (Q.M (D.abelianIndex j)).hom b)), ?_⟩
    have : IsMonHom (ec (D.abelianIndex j)).hom :=
      ArithmeticGeometry.Models.SpreadingOut.GroupBaseChange.Construction.baseChange_comparison_group_hom F G H c (Q.M (D.abelianIndex j))
    have : IsMonHom (Q.e (D.abelianIndex j)).hom := (Q.abelian j).2.2
    exact inferInstanceAs
      (IsMonHom ((ec (D.abelianIndex j)).hom ≫ (Q.e (D.abelianIndex j)).hom))
  · intro a ha
    have : Surjective (Q.fM a).left := Q.preserves_surjectivity a ha
    exact MorphismProperty.of_isPullback (P := @Surjective) (Specialization.base_change_square b (Q.fM a))
      inferInstance

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.SplitLocalizedModels
