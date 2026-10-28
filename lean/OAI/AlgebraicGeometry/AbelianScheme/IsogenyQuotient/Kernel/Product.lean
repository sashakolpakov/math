import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SubgroupFunctor

/-! # Product -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.Product.Construction

/-!
Products of the chosen and opposite kernels as actual relative subgroups.
A lifted block projector separates the two factors. Consequently their
product has a finite locally free geometric model, built as a fiber product
of the individual subgroup models. No quotient or kernel representability
conclusion is assumed in the model construction.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

def subgroupProduct {V : Type*} [CommGroup V] (F G : Subgroup V) : Subgroup V where
  carrier := {a | ∃ x ∈ F, ∃ y ∈ G, a = x * y}
  one_mem' := ⟨1, F.one_mem, 1, G.one_mem, (one_mul 1).symm⟩
  mul_mem' := by
    rintro a b ⟨x, hx, y, hy, rfl⟩ ⟨z, hz, w, hw, rfl⟩
    exact ⟨x * z, F.mul_mem hx hz, y * w, G.mul_mem hy hw, mul_mul_mul_comm x y z w⟩
  inv_mem' := by
    rintro a ⟨x, hx, y, hy, rfl⟩
    exact ⟨x⁻¹, F.inv_mem hx, y⁻¹, G.inv_mem hy, mul_inv x y⟩

variable {S : Scheme.{u}} {A P : Over S} [GrpObj A] [IsCommMonObj A]

/-- Product of commuting subgroups, retaining the actual inclusions. -/
noncomputable def relativeKernelProduct
    (F G : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P where
  points X t := subgroupProduct (F.points X t) (G.points X t)
  naturality := by
    intro X Y f t a ha
    change ∃ x ∈ F.points Y t, ∃ y ∈ G.points Y t, a = x * y at ha
    obtain ⟨x, hx, y, hy, ha⟩ := ha
    change ∃ x ∈ F.points X (f ≫ t), ∃ y ∈ G.points X (f ≫ t), f ≫ a = x * y
    refine ⟨f ≫ x, F.naturality f t hx, f ≫ y, G.naturality f t hy, ?_⟩
    rw [ha, MonObj.comp_mul]

theorem relativeKernelProduct_killed
    (F G : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) (n : ℕ)
    (hF : F.KilledBy n) (hG : G.KilledBy n) :
    (relativeKernelProduct F G).KilledBy n := by
  rintro X t a ⟨x, hx, y, hy, rfl⟩
  rw [mul_pow, hF X t x hx, hG X t y hy, one_mul]

/-- A projector separating two subgroup models makes multiplication
injective, so their relative product is again a subgroup model. -/
noncomputable def relativeKernelProduct_model
    (F G : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) (R : F.Model) (Q : G.Model)
    (projectorLift : A ⟶ A) [IsMonHom projectorLift]
    (hR : R.toGroup ≫ projectorLift = R.toGroup)
    (hQ : Q.toGroup ≫ projectorLift = 1) :
    (relativeKernelProduct F G).Model where
  carrier := pullback R.toBase Q.toBase
  toBase := pullback.fst R.toBase Q.toBase ≫ R.toBase
  toGroup := (pullback.fst R.toBase Q.toBase ≫ R.toGroup) *
    (pullback.snd R.toBase Q.toBase ≫ Q.toGroup)
  finite := by
    have : IsFinite (pullback.fst R.toBase Q.toBase).left :=
      MorphismProperty.of_isPullback
        ((IsPullback.of_hasPullback R.toBase Q.toBase).map (Over.forget S)).flip Q.finite
    have : IsFinite R.toBase.left := R.finite
    change IsFinite ((pullback.fst R.toBase Q.toBase).left ≫ R.toBase.left)
    infer_instance
  flat := by
    have : Flat (pullback.fst R.toBase Q.toBase).left :=
      MorphismProperty.of_isPullback
        ((IsPullback.of_hasPullback R.toBase Q.toBase).map (Over.forget S)).flip Q.flat
    have : Flat R.toBase.left := R.flat
    change Flat ((pullback.fst R.toBase Q.toBase).left ≫ R.toBase.left)
    infer_instance
  finitePresentation := by
    have : LocallyOfFinitePresentation (pullback.fst R.toBase Q.toBase).left :=
      MorphismProperty.of_isPullback
        ((IsPullback.of_hasPullback R.toBase Q.toBase).map (Over.forget S)).flip Q.finitePresentation
    have : LocallyOfFinitePresentation R.toBase.left := R.finitePresentation
    change LocallyOfFinitePresentation ((pullback.fst R.toBase Q.toBase).left ≫ R.toBase.left)
    infer_instance
  jointly_monic X a b hbase hgroup := by
    have hRgroup : a ≫ pullback.fst R.toBase Q.toBase ≫ R.toGroup =
        b ≫ pullback.fst R.toBase Q.toBase ≫ R.toGroup := by
      have h := congrArg (fun t => t ≫ projectorLift) hgroup
      simpa only [MonObj.comp_mul, MonObj.mul_comp, Category.assoc,
        hR, hQ, MonObj.comp_one, mul_one] using h
    have hfst : a ≫ pullback.fst R.toBase Q.toBase =
        b ≫ pullback.fst R.toBase Q.toBase := by
      apply R.jointly_monic X
      · simpa only [Category.assoc] using hbase
      · simpa only [Category.assoc] using hRgroup
    have hQgroup : a ≫ pullback.snd R.toBase Q.toBase ≫ Q.toGroup =
        b ≫ pullback.snd R.toBase Q.toBase ≫ Q.toGroup := by
      simp only [MonObj.comp_mul] at hgroup
      rw [hRgroup] at hgroup
      exact mul_left_cancel hgroup
    have hsnd : a ≫ pullback.snd R.toBase Q.toBase =
        b ≫ pullback.snd R.toBase Q.toBase := by
      apply Q.jointly_monic X
      · simpa only [Category.assoc, ← pullback.condition] using hbase
      · simpa only [Category.assoc] using hQgroup
    exact pullback.hom_ext hfst hsnd
  points_iff X t a := by
    constructor
    · rintro ⟨x, hx, y, hy, ha⟩
      obtain ⟨r, hrbase, hrgroup⟩ := (R.points_iff X t x).mp hx
      obtain ⟨q, hqbase, hqgroup⟩ := (Q.points_iff X t y).mp hy
      let l := pullback.lift r q (hrbase.trans hqbase.symm)
      refine ⟨l, ?_, ?_⟩
      · simpa only [l, ← Category.assoc, pullback.lift_fst] using hrbase
      · simpa only [l, MonObj.comp_mul, ← Category.assoc, pullback.lift_fst,
          pullback.lift_snd, hrgroup, hqgroup] using ha.symm
    · rintro ⟨l, hbase, hgroup⟩
      refine ⟨l ≫ pullback.fst R.toBase Q.toBase ≫ R.toGroup, ?_,
        l ≫ pullback.snd R.toBase Q.toBase ≫ Q.toGroup, ?_, ?_⟩
      · apply (R.points_iff X t _).mpr
        refine ⟨l ≫ pullback.fst R.toBase Q.toBase, ?_, Category.assoc _ _ _⟩
        simpa only [Category.assoc] using hbase
      · apply (Q.points_iff X t _).mpr
        refine ⟨l ≫ pullback.snd R.toBase Q.toBase, ?_, Category.assoc _ _ _⟩
        simpa only [Category.assoc, ← pullback.condition] using hbase
      · simpa only [MonObj.comp_mul] using hgroup.symm

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.Product.Construction
