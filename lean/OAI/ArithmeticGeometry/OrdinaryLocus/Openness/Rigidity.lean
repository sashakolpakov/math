import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FiniteImageNeighborhood
import Mathlib.AlgebraicGeometry.Group.Abelian

/-! # Rigidity -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.Rigidity.Construction

noncomputable section

/-! Rigidity for morphisms out of proper families over an algebraically closed field. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory

universe u

theorem graph_image_fiber_subset_singleton
    {k : Type u} [Field k] [IsAlgClosed k]
    (Y X Z : Over (Spec (.of k)))
    [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Z.hom]
    (y₀ : 𝟙_ (Over (Spec (.of k))) ⟶ Y)
    (z₀ : 𝟙_ (Over (Spec (.of k))) ⟶ Z)
    (f : Y ⊗ X ⟶ Z)
    (h₀ : lift (toUnit X ≫ y₀) (𝟙 X) ≫ f = toUnit X ≫ z₀) :
    (lift (fst Y X) f).left '' ((fst Y X).left ⁻¹'
      {y₀.left (IsLocalRing.closedPoint k)}) ⊆
        {(lift y₀ z₀).left (IsLocalRing.closedPoint k)} := by
  let point : Spec (.of k) := IsLocalRing.closedPoint k
  let γ := lift (fst Y X) f
  have : LocallyOfFiniteType (Y ⊗ X).hom := by dsimp; infer_instance
  have : LocallyOfFiniteType (Y ⊗ Z).hom := by dsimp; infer_instance
  have : JacobsonSpace (Y ⊗ X).left := LocallyOfFiniteType.jacobsonSpace (Y ⊗ X).hom
  have hy₀ : IsClosed {y₀.left point} :=
    ((pointEquivClosedPoint Y.hom) ⟨y₀.left, Over.w y₀⟩).2
  have hz₀ : IsClosed {(lift y₀ z₀).left point} :=
    ((pointEquivClosedPoint (Y ⊗ Z).hom) ⟨(lift y₀ z₀).left, Over.w _⟩).2
  rw [Set.image_subset_iff, ← Set.sdiff_eq_empty, ← Set.not_nonempty_iff_eq_empty]
  intro H
  obtain ⟨c₀, ⟨hc₁, hc₂⟩, hc₃⟩ := nonempty_inter_closedPoints H (by
    rw [Set.sdiff_eq_compl_inter]
    exact ((hz₀.preimage γ.left.continuous).isOpen_compl.isLocallyClosed).inter
      ((hy₀.preimage (fst Y X).left.continuous).isLocallyClosed))
  obtain ⟨⟨c, hc⟩, e⟩ := (pointEquivClosedPoint (Y ⊗ X).hom).surjective ⟨c₀, hc₃⟩
  obtain rfl : c point = c₀ := congr(($e).1)
  let c' : 𝟙_ (Over (Spec (.of k))) ⟶ Y ⊗ X := Over.homMk c hc
  have hfst : c' ≫ fst Y X = y₀ := by
    ext1
    exact ext_of_apply_closedPoint_eq Y.hom (Over.w (c' ≫ fst Y X)) (Over.w y₀) hc₁
  have hfac : c' = (c' ≫ snd Y X) ≫ lift (toUnit X ≫ y₀) (𝟙 X) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [hfst]
  have hγ : c' ≫ γ = lift y₀ z₀ := by
    rw [hfac]
    apply CartesianMonoidalCategory.hom_ext
    · simp [γ]
    · simp only [Category.assoc, γ, lift_snd]
      rw [← Category.assoc, h₀]
      simp
  apply hc₂
  change γ.left (c point) = (lift y₀ z₀).left point
  exact congrArg (fun q : Spec (.of k) ⟶ (Y ⊗ Z).left ↦ q point)
    (congrArg Over.Hom.left hγ)

/-- If a morphism on an integral product is constant on one fiber of its
proper factor, it is independent of that factor. -/
theorem rigidity_of_constant_fiber
    {k : Type u} [Field k] [IsAlgClosed k]
    (Y X Z : Over (Spec (.of k)))
    [LocallyOfFiniteType Y.hom] [IsProper X.hom]
    [LocallyOfFiniteType Z.hom] [IsSeparated Z.hom]
    [IsIntegral (Y ⊗ X).left]
    (y₀ : 𝟙_ (Over (Spec (.of k))) ⟶ Y)
    (x₀ : 𝟙_ (Over (Spec (.of k))) ⟶ X)
    (z₀ : 𝟙_ (Over (Spec (.of k))) ⟶ Z)
    (f : Y ⊗ X ⟶ Z)
    (h₀ : lift (toUnit X ≫ y₀) (𝟙 X) ≫ f = toUnit X ≫ z₀) :
    f = fst Y X ≫ lift (𝟙 Y) (toUnit Y ≫ x₀) ≫ f := by
  let point : Spec (.of k) := IsLocalRing.closedPoint k
  let γ := lift (fst Y X) f
  let r : Y ⊗ X ⟶ Y ⊗ X := fst Y X ≫ lift (𝟙 Y) (toUnit Y ≫ x₀)
  have : Nonempty X.left := ⟨x₀.left point⟩
  have : Nonempty Y.left := ⟨y₀.left point⟩
  have : Surjective X.hom := ⟨Function.surjective_to_subsingleton _⟩
  have : Surjective Y.hom := ⟨Function.surjective_to_subsingleton _⟩
  have : IsProper (fst Y X).left := by dsimp; infer_instance
  have : Surjective (fst Y X).left := by dsimp; infer_instance
  have : IsSeparated (fst Y Z).left := by dsimp; infer_instance
  have : LocallyOfFiniteType (fst Y Z).left := by dsimp; infer_instance
  have : LocallyOfFiniteType (Y ⊗ X).hom := by dsimp; infer_instance
  have : JacobsonSpace (Y ⊗ X).left := LocallyOfFiniteType.jacobsonSpace (Y ⊗ X).hom
  have : IsProper (γ.left ≫ (fst Y Z).left) := by
    simpa only [← Over.comp_left, γ, lift_fst] using
      (inferInstance : IsProper (fst Y X).left)
  have : IsProper γ.left := .of_comp _ (fst Y Z).left
  have hfinite : (γ.left '' ((γ.left ≫ (fst Y Z).left) ⁻¹'
      {y₀.left point})).Finite := by
    rw [← Over.comp_left]
    simpa only [γ, lift_fst] using (Set.finite_singleton _).subset
      (graph_image_fiber_subset_singleton Y X Z y₀ z₀ f h₀)
  obtain ⟨U, hy₀U, hU⟩ :=
    FiniteImageNeighborhood.Construction.finite_image_fiber_neighborhood γ.left (fst Y Z).left (y₀.left point) hfinite
  ext1
  have : LocallyOfFiniteType (f.left ≫ Z.hom) := by rw [Over.w]; infer_instance
  refine ext_of_apply_eq Z.hom _
    ((fst Y X).left ⁻¹ᵁ U).isOpen.isLocallyClosed
    (((fst Y X).left ⁻¹ᵁ U).isOpen.dense ?_) ?_ ?_
  · exact .preimage ⟨_, hy₀U⟩ (fst Y X).left.surjective
  · intro c hcU hc
    have hy : IsClosed {(fst Y X).left c} := by
      simpa only [Set.image_singleton] using (fst Y X).left.isClosedMap _ hc
    let y : 𝟙_ (Over (Spec (.of k))) ⟶ Y :=
      Over.homMk (pointOfClosedPoint Y.hom _ hy) (pointOfClosedPoint_comp Y.hom _ hy)
    let c' : (Y ⊗ X).left := r.left c
    have hr : (fst Y X).left c' = (fst Y X).left c := by
      change (r ≫ fst Y X).left c = _
      simp [r]
    have hγ : γ.left c = γ.left c' := by
      refine subsingleton_image_closure_of_finite_of_isPreirreducible
        (hy.preimage (fst Y X).left.continuous).isLocallyClosed ?_ γ.left.continuous
        γ.left.isClosedMap ((hU ⟨_, hcU⟩).subset (Set.image_subset_iff.mpr ?_)) ?_ ?_
      · let α : Y ⊗ X ⟶ Y ⊗ X := (toUnit Y ≫ y) ⊗ₘ 𝟙 X
        convert!
          ((IrreducibleSpace.isIrreducible_univ _).image α.left
            α.left.continuous.continuousOn).isPreirreducible
        rw [Over.tensorHom_left]
        simp [Set.range_comp, Scheme.Pullback.range_map, y,
          Set.range_eq_univ.mpr Y.hom.surjective]
      · intro t ht
        refine ⟨?_, ⟨t, rfl⟩⟩
        change (γ ≫ fst Y Z).left t = (fst Y X).left c
        change (fst Y X).left t = (fst Y X).left c at ht
        simpa only [γ, lift_fst] using ht
      · exact ⟨c, subset_closure (by simp), rfl⟩
      · exact ⟨c', subset_closure hr, rfl⟩
    have h := congrArg (fun z ↦ (snd Y Z).left z) hγ
    change (γ ≫ snd Y Z).left c = (r ≫ γ ≫ snd Y Z).left c at h
    simpa only [γ, lift_snd, r, Category.assoc] using h
  · exact (Over.w f).trans (Over.w (fst Y X ≫ lift (𝟙 Y) (toUnit Y ≫ x₀) ≫ f)).symm

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.Rigidity.Construction
