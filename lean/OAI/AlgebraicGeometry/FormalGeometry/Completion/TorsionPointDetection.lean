import OAI.AlgebraicGeometry.FormalGeometry.Completion.TorsionPointAction
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SchemeSmooth

/-! # Torsion Point Detection -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.TorsionPointDetection.Construction

noncomputable section

/-! Actual geometric torsion points detect restriction to the actual finite torsion scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- Field-valued points detect actual morphisms from a reduced finite-type geometric scheme. -/
theorem over_hom_ext_of_field_points
    {X Y : Over (Spec (CommRingCat.of K))} [IsReduced X.left]
    [LocallyOfFiniteType X.hom] [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom]
    (f g : X ⟶ Y)
    (h : ∀ a : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ X, a ≫ f = a ≫ g) : f = g := by
  have : LocallyOfFiniteType (f.left ≫ Y.hom) := by rw [f.w]; infer_instance
  apply Over.OverMorphism.ext
  apply ext_of_apply_eq Y.hom Set.univ isOpen_univ.isLocallyClosed dense_univ
  · intro x _ hx
    let a : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ X :=
      Over.homMk (pointOfClosedPoint X.hom x hx) (pointOfClosedPoint_comp X.hom x hx)
    have he := congrArg (fun b : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ Y =>
      b.left (IsLocalRing.closedPoint K)) (h a)
    have ha : a.left (IsLocalRing.closedPoint K) = x :=
      pointOfClosedPoint_apply X.hom x hx (IsLocalRing.closedPoint K)
    change f.left (a.left (IsLocalRing.closedPoint K)) =
      g.left (a.left (IsLocalRing.closedPoint K)) at he
    rw [ha] at he
    exact he
  · exact f.w.trans g.w.symm

variable (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom]

/-- Vanishing on all actual field-valued torsion points is vanishing on the whole torsion scheme. -/
theorem torsion_restriction_eq_one_of_points
    (n : ℕ) (hn : (n : K) ≠ 0) (f : Endomorphisms.Construction.AlgebraicEnd A)
    (hf : TorsionPointAction.Construction.algebraicEndTorsionPointAction A n f = 0) :
    AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n ≫ f.toMul.hom.hom = 1 := by
  have : IsFinite (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme A n).hom := (Multiplication.Construction.torsionScheme_finite_etale A n hn).1
  have : Etale (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme A n).hom := (Multiplication.Construction.torsionScheme_finite_etale A n hn).2
  have : IsReduced (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme A n).left :=
    Quotients.FiniteDescent.SchemeSmooth.Construction.SchemeSmoothReduced.reduced_of_smooth_field (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme A n).hom
  apply over_hom_ext_of_field_points
  intro a
  have ha : (a ≫ AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n) ^ n = 1 :=
    (AbelianScheme.TorsionQuotient.SubgroupFunctor.factors_through_torsion_iff n (a ≫ AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n)).mp ⟨a, rfl⟩
  let t : TorsionPointAction.Construction.geometricTorsionPoints A n := ⟨a ≫ AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n, ha⟩
  have he := congrArg (fun F => F (Additive.ofMul t)) hf
  have hz := congrArg (fun b : Additive (TorsionPointAction.Construction.geometricTorsionPoints A n) => b.toMul.val) he
  change (a ≫ AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n) ≫ f.toMul.hom.hom = 1 at hz
  simpa only [Category.assoc, MonObj.comp_one] using hz

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.TorsionPointDetection.Construction
