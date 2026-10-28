import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Multiplication

/-! # Fiberwise -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Fiberwise.Construction

noncomputable section

/-!
Recover the isogeny properties of a relative homomorphism from its actual
geometric-fiber isogenies. Finiteness is proved from properness and finite
geometric fibers; finite presentation and flatness are then derived.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

theorem finite_targetBaseChange_of_factorization
    {S Z W : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) (t : Z ⟶ S)
    (a : W ⟶ Y.left) (b : W ⟶ Z) (h : a ≫ Y.hom = b ≫ t)
    [IsFinite ((Over.pullback t).map f).left] : IsFinite (pullback.snd f.left a) := by
  let l := pullback.lift a b h
  have hp := ArithmeticGeometry.OrdinaryLocus.Openness.RelativeBaseChange.Construction.isPullback_overPullback_map f t
  have hq : IsPullback (pullback.fst f.left a) (pullback.snd f.left a)
      f.left (l ≫ pullback.fst Y.hom t) := by
    simpa only [l, pullback.lift_fst] using IsPullback.of_hasPullback f.left a
  exact MorphismProperty.of_isPullback (IsPullback.of_right' hq hp) inferInstance

theorem finite_points_of_finite_field_baseChange
    {S : Scheme.{u}} (X : Over S)
    {K : Type u} [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ S)
    [IsFinite (pullback.snd X.hom a)] : Finite (Over.mk a ⟶ X) := by
  have h := (pullback.snd X.hom a).finite_preimage
    (Set.toFinite (Set.univ : Set (Spec (.of K))))
  simp only [Set.preimage_univ] at h
  have : Finite ↥(pullback X.hom a) := Set.finite_univ_iff.mp h
  exact Finite.of_equiv _
    ((ArithmeticGeometry.OrdinaryLocus.Openness.Multiplication.Construction.fieldPointPullbackEquiv X a).trans (pointEquivClosedPoint (pullback.snd X.hom a))).symm

/-- A proper relative morphism with finite geometric base changes is
finite, without any flatness or reducedness premise on the base. -/
theorem finite_of_proper_of_finite_geometric_baseChanges
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) [IsProper f.left]
    (hfiber : ∀ (K : Type u) [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ S),
      IsFinite ((Over.pullback t).map f).left) : IsFinite f.left := by
  have : LocallyQuasiFinite f.left := by
    apply LocallyQuasiFinite.of_finite_preimage_singleton
    intro y
    let a := (ArithmeticGeometry.OrdinaryLocus.Openness.DefinitionsTorsion.geometricPoint Y.left y).hom
    let t := a ≫ Y.hom
    have : IsFinite ((Over.pullback t).map f).left :=
      hfiber (AlgebraicClosure (Y.left.residueField y)) t
    have hfinite : IsFinite (pullback.snd f.left a) :=
      finite_targetBaseChange_of_factorization f t a (𝟙 _) (Category.id_comp _).symm
    have : IsFinite (pullback.snd (Over.mk f.left).hom a) := hfinite
    have : LocallyOfFiniteType (Over.mk f.left).hom := inferInstanceAs (LocallyOfFiniteType f.left)
    have : Finite (ArithmeticGeometry.OrdinaryLocus.Openness.DefinitionsTorsion.geometricPoint Y.left y ⟶ Over.mk f.left) :=
      @finite_points_of_finite_field_baseChange Y.left (Over.mk f.left)
        (AlgebraicClosure (Y.left.residueField y)) inferInstance inferInstance a hfinite
    exact ArithmeticGeometry.OrdinaryLocus.Openness.DefinitionsTorsion.Construction.finite_preimage_of_finite_geometric_points (Over.mk f.left) y
  exact IsFinite.of_isProper_of_locallyQuasiFinite f.left

/-- Isogeny geometry is a consequence of the geometric-fiber isogenies,
not extra relative data supplied to the polarization construction. -/
def isogenyFromGeometricFibers
    {S : Scheme.{u}} (A B : Picard.PoincareBundle.Epi.Construction.AbelianScheme S)
    (f : A.toOver ⟶ B.toOver) [IsMonHom f]
    (hfiber : ∀ (K : Type u) [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ S),
      IsFinite ((Over.pullback t).map f).left ∧
        Flat ((Over.pullback t).map f).left ∧ Surjective ((Over.pullback t).map f).left) :
    Picard.PoincareBundle.Epi.Construction.AbelianScheme.Isogeny A B := by
  have : IsProper (f.left ≫ B.toOver.hom) := by rw [f.w]; infer_instance
  have : IsProper f.left := IsProper.of_comp f.left B.toOver.hom
  have : IsFinite f.left :=
    finite_of_proper_of_finite_geometric_baseChanges f (fun K _ _ t => (hfiber K t).1)
  have : LocallyOfFinitePresentation (f.left ≫ B.toOver.hom) := by rw [f.w]; infer_instance
  have : LocallyOfFinitePresentation f.left :=
    ArithmeticGeometry.OrdinaryLocus.Openness.FinitePresentation.Construction.locallyOfFinitePresentation_of_comp_of_locallyOfFiniteType f.left B.toOver.hom
  have : Flat f.left := ArithmeticGeometry.OrdinaryLocus.Openness.FiberwiseFlatness.Construction.flat_finite_of_flat_geometric_baseChanges f
    (fun K _ _ t => (hfiber K t).2.1)
  have : Surjective f.left := Multiplication.Construction.surjective_of_geometric_baseChanges f
    (fun K _ _ t => (hfiber K t).2.2)
  exact {
    hom := f
    isMonHom := inferInstance
    finite := inferInstance
    flat := inferInstance
    surjective := inferInstance
    finitePresentation := inferInstance }

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Fiberwise.Construction
