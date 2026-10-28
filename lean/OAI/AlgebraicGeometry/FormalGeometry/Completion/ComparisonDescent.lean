import OAI.AlgebraicGeometry.FormalGeometry.Completion.FunctionsComparison

/-! # Comparison Descent -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.ComparisonDescent.Construction

noncomputable section

/-! The actual formal-functions comparison descends along a map detecting infinitesimal sections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {R : Type u} [CommRing R] (I : Ideal R) {X Y : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ X)

/-- The literal base change of a family morphism to each infinitesimal level. -/
def infinitesimalNeighborhoodMap (n : ℕ) :
    Infinitesimal.Neighborhoods.Construction.infinitesimalNeighborhood I (g ≫ f) n ⟶ Infinitesimal.Neighborhoods.Construction.infinitesimalNeighborhood I f n :=
  pullback.map _ _ _ _ g (𝟙 _) (𝟙 _) (by simp) (by simp)

@[reassoc]
theorem infinitesimalNeighborhoodMap_snd (n : ℕ) :
    infinitesimalNeighborhoodMap I f g n ≫ pullback.snd f (Infinitesimal.Neighborhoods.Construction.infinitesimalBaseToSpec I n) =
      pullback.snd (g ≫ f) (Infinitesimal.Neighborhoods.Construction.infinitesimalBaseToSpec I n) := by
  simp [infinitesimalNeighborhoodMap]

@[reassoc]
theorem infinitesimalNeighborhoodMap_fst (n : ℕ) :
    infinitesimalNeighborhoodMap I f g n ≫ pullback.fst f (Infinitesimal.Neighborhoods.Construction.infinitesimalBaseToSpec I n) =
      pullback.fst (g ≫ f) (Infinitesimal.Neighborhoods.Construction.infinitesimalBaseToSpec I n) ≫ g := by
  simp [infinitesimalNeighborhoodMap]

theorem infinitesimalNeighborhoodMap_isPullback (n : ℕ) :
    IsPullback (infinitesimalNeighborhoodMap I f g n)
      (pullback.fst (g ≫ f) (Infinitesimal.Neighborhoods.Construction.infinitesimalBaseToSpec I n))
      (pullback.fst f (Infinitesimal.Neighborhoods.Construction.infinitesimalBaseToSpec I n)) g := by
  refine .of_right (t := (IsPullback.of_hasPullback f (Infinitesimal.Neighborhoods.Construction.infinitesimalBaseToSpec I n)).flip) ?_ ?_
  · simpa [infinitesimalNeighborhoodMap] using
      (IsPullback.of_hasPullback (g ≫ f) (Infinitesimal.Neighborhoods.Construction.infinitesimalBaseToSpec I n)).flip
  · simp [infinitesimalNeighborhoodMap]

theorem infinitesimalNeighborhoodMap_transition (n : ℕ) :
    Infinitesimal.Neighborhoods.Construction.infinitesimalTransition I (g ≫ f) n ≫ infinitesimalNeighborhoodMap I f g (n + 1) =
      infinitesimalNeighborhoodMap I f g n ≫ Infinitesimal.Neighborhoods.Construction.infinitesimalTransition I f n := by
  apply pullback.hom_ext <;> simp [infinitesimalNeighborhoodMap, Infinitesimal.Neighborhoods.Construction.infinitesimalTransition]

/-- Pullback on the actual compatible infinitesimal section rings. -/
def infinitesimalGlobalSectionsPullback :
    Infinitesimal.ClopenSections.Construction.infinitesimalGlobalSections I f →+* Infinitesimal.ClopenSections.Construction.infinitesimalGlobalSections I (g ≫ f) where
  toFun s := ⟨fun n => (infinitesimalNeighborhoodMap I f g n).appTop (s.val n), fun n => by
    change ((infinitesimalNeighborhoodMap I f g (n + 1)).appTop ≫
      (Infinitesimal.Neighborhoods.Construction.infinitesimalTransition I (g ≫ f) n).appTop) (s.val (n + 1)) = _
    rw [← Scheme.Hom.comp_appTop, infinitesimalNeighborhoodMap_transition, Scheme.Hom.comp_appTop]
    exact congrArg ((infinitesimalNeighborhoodMap I f g n).appTop) (s.property n)⟩
  map_zero' := by apply Subtype.ext; funext n; exact map_zero _
  map_one' := by apply Subtype.ext; funext n; exact map_one _
  map_add' x y := by apply Subtype.ext; funext n; exact map_add _ _ _
  map_mul' x y := by apply Subtype.ext; funext n; exact map_mul _ _ _

theorem infinitesimalGlobalSectionsPullback_injective
    (h : ∀ n, Function.Injective (infinitesimalNeighborhoodMap I f g n).appTop) :
    Function.Injective (infinitesimalGlobalSectionsPullback I f g) := by
  intro s t hst
  apply Subtype.ext
  funext n
  exact h n (congrArg (fun z : Infinitesimal.ClopenSections.Construction.infinitesimalGlobalSections I (g ≫ f) => z.val n) hst)

/-- The actual formal-functions map commutes with pullback of the family. -/
theorem formalFunctionsComparison_pullback (x : AdicCompletion I R) :
    infinitesimalGlobalSectionsPullback I f g (FunctionsComparison.Construction.formalFunctionsComparison I f x) =
      FunctionsComparison.Construction.formalFunctionsComparison I (g ≫ f) x := by
  apply Subtype.ext
  funext n
  change (((Scheme.ΓSpecIso (.of (R ⧸ I ^ (n + 1)))).inv ≫
    (pullback.snd f (Infinitesimal.Neighborhoods.Construction.infinitesimalBaseToSpec I n)).appTop) ≫
      (infinitesimalNeighborhoodMap I f g n).appTop) (AdicCompletion.evalₐ I (n + 1) x) = _
  rw [Category.assoc, ← Scheme.Hom.comp_appTop, infinitesimalNeighborhoodMap_snd]
  rfl

theorem formalFunctionsComparison_surjective_of_detecting_pullback
    (hg : ∀ n, Function.Injective (infinitesimalNeighborhoodMap I f g n).appTop)
    (h : Function.Surjective (FunctionsComparison.Construction.formalFunctionsComparison I (g ≫ f))) :
    Function.Surjective (FunctionsComparison.Construction.formalFunctionsComparison I f) := by
  intro s
  obtain ⟨x, hx⟩ := h (infinitesimalGlobalSectionsPullback I f g s)
  refine ⟨x, infinitesimalGlobalSectionsPullback_injective I f g hg ?_⟩
  rw [formalFunctionsComparison_pullback]
  exact hx

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.ComparisonDescent.Construction
