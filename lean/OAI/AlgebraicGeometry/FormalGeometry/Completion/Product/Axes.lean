import OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.PointCohomology
import OAI.AlgebraicGeometry.FormalGeometry.Completion.GroupLawCohomology

/-! # Axes -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.Axes.Construction

noncomputable section

/-!
# Completion: restriction of the group-law defect to the product axes

Constant maps act by zero on actual geometric H¹. Consequently the
group-law defect restricts to zero on each product axis. This does not yet
assert joint injectivity of the two restriction maps.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]

/-- A constant morphism over k pulls back to zero on actual geometric H¹. -/
theorem geometricH1Pullback_constant {A B : Over (Spec (CommRingCat.of k))}
    (e : Spec (CommRingCat.of k) ⟶ B.left) (he : e ≫ B.hom = 𝟙 _)
    (f : A ⟶ B) (hf : f.left = A.hom ≫ e) : Endomorphism.Action.Construction.geometricH1Pullback ℓ k f = 0 := by
  let ebar : Spec (CommRingCat.of (AlgebraicClosure k)) ⟶ Cohomology.Construction.geometricFiber B :=
    pullback.lift (Geometric.Frobenius.Construction.algebraicClosureBase k ≫ e) (𝟙 _) (by simp [Category.assoc, he])
  have hmap : Geometric.Frobenius.Construction.geometricFiberMap k f =
      pullback.snd A.hom (Geometric.Frobenius.Construction.algebraicClosureBase k) ≫ ebar := by
    apply pullback.hom_ext
    · simp only [Geometric.Frobenius.Construction.geometricFiberMap_fst, Category.assoc, ebar, pullback.lift_fst]
      rw [hf, ← Category.assoc, pullback.condition]
      simp only [Category.assoc]
    · simp only [Geometric.Frobenius.Construction.geometricFiberMap_snd, Category.assoc, ebar, pullback.lift_snd,
        Category.comp_id]
  unfold Endomorphism.Action.Construction.geometricH1Pullback
  rw [hmap]
  exact Geometric.PointCohomology.Construction.algebraicEllAdicH1Pullback_through_geometricPoint (AlgebraicClosure k) ℓ _ _

variable (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsCommMonObj A]

/-- The zero algebraic endomorphism acts by zero on actual geometric H¹. -/
theorem geometricH1Pullback_zero_end :
    Endomorphism.Action.Construction.geometricH1Pullback ℓ k (0 : Endomorphisms.Construction.AlgebraicEnd A).toMul.hom.hom = 0 := by
  apply geometricH1Pullback_constant ℓ k (η[A]).left
  · exact (η[A]).w
  · rfl

/-- The first product axis, with the second coordinate the identity section. -/
abbrev groupFirstAxis : A ⟶ A ⊗ A := lift (𝟙 A) (toUnit A ≫ η[A])

/-- The second product axis, with the first coordinate the identity section. -/
abbrev groupSecondAxis : A ⟶ A ⊗ A := lift (toUnit A ≫ η[A]) (𝟙 A)

/-- The group-law defect restricts to zero on the first axis. -/
theorem geometricH1GroupLawDefect_firstAxis :
    (Endomorphism.Action.Construction.geometricH1Pullback ℓ k (groupFirstAxis k A)).comp
      (GroupLawCohomology.Construction.geometricH1GroupLawDefect ℓ k A) = 0 := by
  have hz : Endomorphism.Action.Construction.geometricH1Pullback ℓ k (toUnit A ≫ η[A]) = 0 :=
    geometricH1Pullback_zero_end ℓ k A
  simp only [GroupLawCohomology.Construction.geometricH1GroupLawDefect, LinearMap.comp_sub, LinearMap.comp_add,
    ← Endomorphism.Action.Construction.geometricH1Pullback_comp, groupFirstAxis, lift_comp_one_right, lift_fst, lift_snd,
    Endomorphism.Action.Construction.geometricH1Pullback_id, hz, add_zero]
  apply LinearMap.ext
  intro x
  exact _root_.sub_self x

/-- The group-law defect restricts to zero on the second axis. -/
theorem geometricH1GroupLawDefect_secondAxis :
    (Endomorphism.Action.Construction.geometricH1Pullback ℓ k (groupSecondAxis k A)).comp
      (GroupLawCohomology.Construction.geometricH1GroupLawDefect ℓ k A) = 0 := by
  have hz : Endomorphism.Action.Construction.geometricH1Pullback ℓ k (toUnit A ≫ η[A]) = 0 :=
    geometricH1Pullback_zero_end ℓ k A
  simp only [GroupLawCohomology.Construction.geometricH1GroupLawDefect, LinearMap.comp_sub, LinearMap.comp_add,
    ← Endomorphism.Action.Construction.geometricH1Pullback_comp, groupSecondAxis, lift_comp_one_left, lift_fst, lift_snd,
    Endomorphism.Action.Construction.geometricH1Pullback_id, hz, zero_add]
  apply LinearMap.ext
  intro x
  exact _root_.sub_self x

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.Axes.Construction
