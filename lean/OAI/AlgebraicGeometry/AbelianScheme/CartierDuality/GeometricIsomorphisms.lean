import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.GeometricFiniteness
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.MultiplicationFlat
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-! # Geometric Isomorphisms -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.GeometricIsomorphisms.Construction.Schemes

noncomputable section

/-!
# CartierDuality: geometric fibers detect isomorphisms of finite locally free schemes
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

/-- A morphism between finite locally free schemes is an isomorphism
if all its algebraically closed base changes are isomorphisms. -/
theorem isIso_of_algClosed_baseChanges {S : Scheme.{u}} {X Y : Over S}
    [IsFinite X.hom] [Flat X.hom] [LocallyOfFinitePresentation X.hom]
    [IsFinite Y.hom] [Flat Y.hom] [LocallyOfFinitePresentation Y.hom]
    (f : X ⟶ Y)
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ S),
      IsIso ((Over.pullback a).map f).left) : IsIso f.left := by
  have : IsFinite (f.left ≫ Y.hom) := by rw [f.w]; infer_instance
  have : IsFinite f.left := IsFinite.of_comp f.left Y.hom
  have hfp : LocallyOfFinitePresentation (f.left ≫ Y.hom) := by rw [f.w]; infer_instance
  have : LocallyOfFinitePresentation f.left :=
    Picard.Homomorphisms.FinitePresentation.Construction.locallyOfFinitePresentation_of_comp_of_finiteType hfp inferInstance
  have : Flat f.left := ArithmeticGeometry.OrdinaryLocus.Openness.FiberwiseFlatness.Construction.flat_finite_of_flat_geometric_baseChanges f (by
    intro K _ _ a
    have := h K a
    infer_instance)
  apply (Scheme.Hom.isIso_iff_finrank_eq f.left).mpr
  funext y
  let K := AlgebraicClosure (Y.left.residueField y)
  let v : Spec (.of K) ⟶ Y.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (Y.left.residueField y) K)) ≫
      Y.left.fromSpecResidueField y
  let a := v ≫ Y.hom
  let j : Spec (.of K) ⟶ pullback Y.hom a := pullback.lift v (𝟙 _) (by simp [a])
  let y' := j (IsLocalRing.closedPoint K)
  have hy : pullback.fst Y.hom a y' = y := by
    have hj : j ≫ pullback.fst Y.hom a = v := pullback.lift_fst _ _ _
    have hv : v (IsLocalRing.closedPoint K) = y := Y.left.fromSpecResidueField_apply y _
    exact (congrArg (fun g : Spec (.of K) ⟶ Y.left => g (IsLocalRing.closedPoint K)) hj).trans hv
  let fp := ((Over.pullback a).map f).left
  have : IsIso fp := h K a
  have hr : fp.finrank y' = f.left.finrank (pullback.fst Y.hom a y') :=
    Scheme.Hom.finrank_of_isPullback _ _ _ _ (LocalIsomorphismsIs.Construction.LocalIsomorphisms.pullbackMap_isPullback a f) y'
  rw [hy] at hr
  exact hr.symm.trans (congrFun (Scheme.Hom.finrank_eq_one_of_isIso fp) y')

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.GeometricIsomorphisms.Construction.Schemes
