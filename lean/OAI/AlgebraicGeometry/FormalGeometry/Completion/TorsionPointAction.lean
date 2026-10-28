import OAI.AlgebraicGeometry.FormalGeometry.Completion.Multiplication

/-! # Torsion Point Action -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.TorsionPointAction.Construction

noncomputable section

/-! Actual finite torsion points and the endomorphism ring acting on them. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {K : Type u} [Field K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]

/-- The actual field-valued points killed by multiplication by n. -/
def geometricTorsionPoints (n : ℕ) : Subgroup (𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A) :=
  (powMonoidHom n).ker

/-- Postcomposition by an actual group endomorphism preserves actual torsion points. -/
def algebraicEndTorsionPointMap (n : ℕ) (f : Endomorphisms.Construction.AlgebraicEnd A) :
    geometricTorsionPoints A n →* geometricTorsionPoints A n where
  toFun a := ⟨a.val ≫ f.toMul.hom.hom, by
    change (a.val ≫ f.toMul.hom.hom) ^ n = 1
    rw [← MonObj.pow_comp, show a.val ^ n = 1 from a.property, MonObj.one_comp]⟩
  map_one' := Subtype.ext (MonObj.one_comp _)
  map_mul' a b := Subtype.ext (MonObj.mul_comp _ _ _)

/-- The genuine endomorphism ring acts on the additive finite torsion group. -/
def algebraicEndTorsionPointAction (n : ℕ) :
    Endomorphisms.Construction.AlgebraicEnd A →+* AddMonoid.End (Additive (geometricTorsionPoints A n)) where
  toFun f := (algebraicEndTorsionPointMap A n f).toAdditive
  map_one' := by
    apply AddMonoidHom.ext
    intro a
    apply Additive.toMul.injective
    apply Subtype.ext
    exact Category.comp_id _
  map_mul' f g := by
    apply AddMonoidHom.ext
    intro a
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (Category.assoc _ _ _).symm
  map_zero' := by
    apply AddMonoidHom.ext
    intro a
    apply Additive.toMul.injective
    apply Subtype.ext
    exact MonObj.comp_one _
  map_add' f g := by
    apply AddMonoidHom.ext
    intro a
    apply Additive.toMul.injective
    apply Subtype.ext
    exact MonObj.comp_mul _ _ _

variable [IsAlgClosed K]

/-- A finite scheme over an algebraically closed field has finitely many actual field points. -/
theorem finite_field_points (T : Over (Spec (CommRingCat.of K))) [IsFinite T.hom] :
    Finite (𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ T) := by
  have hu : (Set.univ : Set T.left).Finite :=
    (T.hom.finite_preimage_singleton (IsLocalRing.closedPoint K)).subset
      (fun _ _ => Subsingleton.elim _ _)
  have : Finite T.left := Set.finite_univ_iff.mp hu
  apply Finite.of_injective (fun f : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ T =>
    f.left (IsLocalRing.closedPoint K))
  intro f g h
  apply Over.OverMorphism.ext
  exact ext_of_apply_closedPoint_eq T.hom f.w g.w h

/-- Finiteness comes from the actual finite scheme-theoretic torsion kernel. -/
theorem geometricTorsionPoints_finite [IsProper A.hom] [Smooth A.hom]
    (n : ℕ) (hn : (n : K) ≠ 0) : Finite (geometricTorsionPoints A n) := by
  have : IsFinite (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme A n).hom := (Multiplication.Construction.torsionScheme_finite_etale A n hn).1
  have := finite_field_points (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme A n)
  let t : geometricTorsionPoints A n →
      (𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme A n) :=
    fun a => AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift n a.val a.property
  apply Finite.of_injective t
  intro a b h
  apply Subtype.ext
  have he := congrArg (fun f => f ≫ AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n) h
  simpa only [t, AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift_ι] using he

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.TorsionPointAction.Construction
