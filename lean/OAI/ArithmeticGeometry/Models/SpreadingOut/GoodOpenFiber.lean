import OAI.ArithmeticGeometry.Models.SpreadingOut.DenseOpen

/-! # Good Open Fiber -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.GoodOpenFiber.Construction

noncomputable section

/-! A geometrically irreducible open controls the fibers of an integral
ambient scheme after shrinking a Dedekind base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem geometricallyIrreducible_after_localization_of_fiber_property
    (R : Type u) [CommRing R] (X : Over (Spec (.of R))) (r : R)
    (h : ∀ (k : Type u) [Field k] [Algebra R k], IsUnit (algebraMap R k r) →
      IrreducibleSpace (pullback X.hom (Spec.map (CommRingCat.ofHom (algebraMap R k))) : Scheme.{u})) :
    GeometricallyIrreducible (pullback.snd X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))))) := by
  refine ⟨fun k _ y Z p q hp ↦ ?_⟩
  obtain ⟨φ, rfl⟩ := Spec.map_surjective y
  let ψ : R →+* k := φ.hom.comp (algebraMap R (Localization.Away r))
  let : Algebra R k := ψ.toAlgebra
  have hu : IsUnit (algebraMap R k r) :=
    (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away r) r).map φ.hom
  have hirr := h k hu
  have houter := hp.paste_horiz (IsPullback.of_hasPullback X.hom
    (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))))
  have he : Spec.map φ ≫ Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))) =
      Spec.map (CommRingCat.ofHom (algebraMap R k)) := by
    rw [← Spec.map_comp]
    rfl
  rw [he] at houter
  exact houter.isoPullback.hom.homeomorph.irreducibleSpace_iff.mpr hirr

theorem geometricallyIrreducible_ambient_after_shrinking
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    {W X : Over (Spec (.of R))} (i : W ⟶ X) [IsOpenImmersion i.left]
    [GeometricallyIrreducible W.hom] [IsIntegral X.left]
    [CompactSpace X.left] [IsLocallyNoetherian X.left] :
    ∃ r : R, r ≠ 0 ∧ GeometricallyIrreducible (pullback.snd X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))))) := by
  classical
  have hn : Nonempty W.left := by
    obtain ⟨w, -⟩ := W.hom.surjective (Classical.choice (inferInstanceAs (Nonempty (Spec (.of R)))))
    exact ⟨w⟩
  let U := i.left.opensRange
  have hU : (U : Set X.left).Nonempty := Set.range_nonempty i.left
  obtain ⟨r, hr, hd⟩ := DenseOpen.Construction.integral_scheme_open_dense_in_fibers_after_shrinking R X U hU
  refine ⟨r, hr, geometricallyIrreducible_after_localization_of_fiber_property R X r ?_⟩
  intro k _ _ hu
  let g := Spec.map (CommRingCat.ofHom (algebraMap R k))
  let F := Over.pullback g
  have : IrreducibleSpace (F.obj W).left :=
    pullback_of_geometrically GeometricallyIrreducible.geometrically_irreducibleSpace k g
  have hj : Set.range (F.map i).left = (pullback.fst X.hom g) ⁻¹' (U : Set X.left) :=
    GeometricFieldComponents.Construction.pullback_square_range_fst (FoundationsPullback.Constructions.pullback_over_map_isPullback g i)
  have : IsDominant (F.map i).left := ⟨by rw [DenseRange, hj]; exact hd k hu⟩
  exact GeometricFieldComponents.Construction.irreducibleSpace_of_dominant (F.map i).left

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.GoodOpenFiber.Construction
