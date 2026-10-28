import OAI.AlgebraicGeometry.Divisors.LineBundles.ValuativeCenterIs

/-! # Model Image Of -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.ModelImageOf.BundleCycles.ModelImage

noncomputable section

/-! A point belongs to a birational affine model's image whenever the
model's coordinate ring embeds in its stalk through the actual function
field. Separatedness identifies the two resulting stalk maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Scheme

universe u

theorem mem_range_of_stalk_lift {X : Scheme.{u}} [IsIntegral X] [X.IsSeparated]
    (A : Type u) [CommRing A] [Algebra A X.functionField]
    (i : Spec (.of A) ⟶ X)
    (hi : Spec.map (CommRingCat.ofHom (algebraMap A X.functionField)) ≫ i = IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap X)
    (x : X) (j : A →+* X.presheaf.stalk x)
    (hj : (algebraMap (X.presheaf.stalk x) X.functionField).comp j = algebraMap A X.functionField) :
    x ∈ Set.range i := by
  let t := Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField))
  let : IsDominant t := by
    refine ⟨?_⟩
    change DenseRange (PrimeSpectrum.comap (algebraMap (X.presheaf.stalk x) X.functionField))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective _ _)]
    exact bot_le
  have he : Spec.map (CommRingCat.ofHom j) ≫ i = X.fromSpecStalk x := by
    apply ext_of_isDominant (ι := t)
    dsimp only [t]
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, hj, hi]
    exact (Scheme.SpecMap_stalkSpecializes_fromSpecStalk
      ((genericPoint_spec X).specializes trivial)).symm
  refine ⟨Spec.map (CommRingCat.ofHom j) (IsLocalRing.closedPoint (X.presheaf.stalk x)), ?_⟩
  change (Spec.map (CommRingCat.ofHom j) ≫ i) _ = x
  rw [he]
  exact Scheme.fromSpecStalk_closedPoint

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.ModelImageOf.BundleCycles.ModelImage
