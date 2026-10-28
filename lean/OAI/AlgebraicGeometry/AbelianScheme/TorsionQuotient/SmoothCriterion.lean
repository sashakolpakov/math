import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SmoothLocal

/-! # Smooth Criterion -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SmoothCriterion.SchemeSmoothCriterion

/-!
# TorsionQuotient: local infinitesimal scheme lifts imply smoothness

At each source point, the universal square-zero extension of its local ring
is tested. The resulting scheme lift gives an actual section of the local
ring extension, so the stalk map is formally smooth.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem stalk_formallySmooth_of_local_lifts {X Y : Scheme.{u}} (f : X ⟶ Y)
    (H : ∀ (C B : CommRingCat.{u}) [IsLocalRing C] [IsLocalRing B]
      (p : C ⟶ B), Function.Surjective p → RingHom.ker p.hom ^ 2 = ⊥ →
      ∀ (a : Spec B ⟶ X) (b : Spec C ⟶ Y), a ≫ f = Spec.map p ≫ b →
        ∃ l : Spec C ⟶ X, Spec.map p ≫ l = a ∧ l ≫ f = b)
    (x : X) : (f.stalkMap x).hom.FormallySmooth := by
  let R := Y.presheaf.stalk (f x)
  let A := X.presheaf.stalk x
  let : Algebra R A := (f.stalkMap x).hom.toAlgebra
  change Algebra.FormallySmooth R A
  apply LocalSmooth.LocalSmoothCriterion.formallySmooth_of_local_sections
  intro C hC hRC hlocal p hp hker
  let p' := CommRingCat.ofHom p.toRingHom
  let b' := CommRingCat.ofHom (algebraMap R C)
  let : IsLocalHom p.toRingHom :=
    LocalSmooth.LocalSmoothCriterion.isLocalHom_of_surjective_squareZero p.toRingHom hp hker
  let : IsLocalHom p'.hom := inferInstanceAs (IsLocalHom p.toRingHom)
  have hbp : b' ≫ p' = f.stalkMap x := by
    ext r
    exact p.commutes r
  let : IsLocalHom (p.toRingHom.comp (algebraMap R C)) := by
    have he : p.toRingHom.comp (algebraMap R C) = (f.stalkMap x).hom :=
      congrArg CommRingCat.Hom.hom hbp
    exact he.symm ▸ (inferInstance : IsLocalHom (f.stalkMap x).hom)
  let : IsLocalHom b'.hom := isLocalHom_of_comp (algebraMap R C) p.toRingHom
  have hab : X.fromSpecStalk x ≫ f = Spec.map p' ≫ (Spec.map b' ≫ Y.fromSpecStalk (f x)) := by
    rw [← Scheme.SpecMap_stalkMap_fromSpecStalk f, ← Spec.map_comp_assoc, hbp]
  obtain ⟨l, hl, hlf⟩ := H (.of C) A p' hp hker (X.fromSpecStalk x)
    (Spec.map b' ≫ Y.fromSpecStalk (f x)) hab
  obtain ⟨⟨y, ⟨v, hv⟩⟩, rfl⟩ := (SpecToEquivOfLocalRing X (.of C)).symm.surjective l
  let : IsLocalHom v.hom := hv
  change Spec.map p' ≫ LocalLifts.LocalSchemeLifts.ofGerm X y v = X.fromSpecStalk x at hl
  have hy : y = x := by
    have he := congrArg (fun z : Spec A ⟶ X => z (IsLocalRing.closedPoint A)) hl
    change LocalLifts.LocalSchemeLifts.ofGerm X y v (Spec.map p' (IsLocalRing.closedPoint A)) =
      X.fromSpecStalk x (IsLocalRing.closedPoint A) at he
    rw [Spec_closedPoint, LocalLifts.LocalSchemeLifts.ofGerm_closedPoint, Scheme.fromSpecStalk_closedPoint] at he
    exact he
  subst y
  let : IsLocalHom (v ≫ p').hom := by
    change IsLocalHom (p'.hom.comp v.hom)
    infer_instance
  have hlp : v ≫ p' = 𝟙 A := by
    apply LocalLifts.LocalSchemeLifts.ofGerm_injective x
    calc
      LocalLifts.LocalSchemeLifts.ofGerm X x (v ≫ p') = X.fromSpecStalk x := by
        exact (Spec.map_comp_assoc v p' (X.fromSpecStalk x)).trans hl
      _ = LocalLifts.LocalSchemeLifts.ofGerm X x (𝟙 A) := by
        exact ((congrArg (fun t : Spec A ⟶ Spec A => t ≫ X.fromSpecStalk x)
          (Spec.map_id A)).trans (Category.id_comp _)).symm
  let : IsLocalHom (f.stalkMap x ≫ v).hom := by
    change IsLocalHom (v.hom.comp (f.stalkMap x).hom)
    infer_instance
  have hfl : f.stalkMap x ≫ v = b' := by
    apply LocalLifts.LocalSchemeLifts.ofGerm_injective (f x)
    rw [LocalLifts.LocalSchemeLifts.ofGerm_comp]
    exact hlf
  let g : A →ₐ[R] C :=
    { v.hom with commutes' := fun r => congrArg (fun z => z.hom r) hfl }
  refine ⟨g, ?_⟩
  ext a
  exact congrArg (fun z => z.hom a) hlp

/-- Finite presentation plus local square-zero scheme lifting gives the
standard smooth-morphism predicate. -/
theorem smooth_of_local_lifts {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (H : ∀ (C B : CommRingCat.{u}) [IsLocalRing C] [IsLocalRing B]
      (p : C ⟶ B), Function.Surjective p → RingHom.ker p.hom ^ 2 = ⊥ →
      ∀ (a : Spec B ⟶ X) (b : Spec C ⟶ Y), a ≫ f = Spec.map p ≫ b →
        ∃ l : Spec C ⟶ X, Spec.map p ≫ l = a ∧ l ≫ f = b) : Smooth f := by
  apply f.smoothLocus_eq_top_iff.mp
  apply top_unique
  intro x _
  exact stalk_formallySmooth_of_local_lifts f H x

end OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SmoothCriterion.SchemeSmoothCriterion
