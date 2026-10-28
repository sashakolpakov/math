import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.HomOpenCoverDetection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.AffineTestMorphisms

/-! # Iso Cocycle Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.IsoCocycleDetection.AffineIsoCocycleDetection

noncomputable section

/-! Generic conjugation and affine-test detection of isomorphism laws. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u v w u₁ u₂ v₁ v₂

theorem pullbackLift_exists {C : Type v} [Category.{w} C]
    {W A B Z T : C} {l : W ⟶ A} {r : W ⟶ B} {p : A ⟶ Z} {q : B ⟶ Z}
    (H : IsPullback l r p q) (a : T ⟶ A) (b : T ⟶ B) (h : a ≫ p = b ≫ q) :
    ∃ c : T ⟶ W, c ≫ l = a ∧ c ≫ r = b :=
  ⟨H.lift a b h, H.lift_fst a b h, H.lift_snd a b h⟩

theorem tripleFactorization_of_arrow_eq {C : Type v} [Category.{w} C]
    {W A B D T : C} {a₀ a₁ : W ⟶ A} {b₀ b₁ : W ⟶ B} {c₀ c₁ : W ⟶ D}
    (ha : a₀ = a₁) (hb : b₀ = b₁) (hc : c₀ = c₁)
    {a : T ⟶ A} {b : T ⟶ B} {c : T ⟶ D}
    (h : ∃ t : T ⟶ W, t ≫ a₁ = a ∧ t ≫ b₁ = b ∧ t ≫ c₁ = c) :
    ∃ t : T ⟶ W, t ≫ a₀ = a ∧ t ≫ b₀ = b ∧ t ≫ c₀ = c := by
  subst a₀
  subst b₀
  subst c₀
  exact h

theorem isoConjugation_injective {C : Type v} [Category.{w} C]
    {A A' B B' : C} (a : A' ≅ A) (b : B' ≅ B) :
    Function.Injective (fun e : A ≅ B => a ≪≫ e ≪≫ b.symm) := by
  intro e f h
  have hh := congrArg (fun t : A' ≅ B' => a.symm ≪≫ t ≪≫ b) h
  simpa only [Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.symm_self_id,
    Iso.trans_refl] using hh

theorem isoSelf_of_conjugate {C : Type v} [Category.{w} C]
    {A A' : C} (a : A' ≅ A) (e : A ≅ A)
    (h : a ≪≫ e ≪≫ a.symm = Iso.refl A') : e = Iso.refl A := by
  apply isoConjugation_injective a a
  simpa only [Iso.refl_trans, Iso.self_symm_id] using h

theorem isoCocycle_of_conjugate {C : Type v} [Category.{w} C]
    {A A' B B' D D' : C} (a : A' ≅ A) (b : B' ≅ B) (d : D' ≅ D)
    (e : A ≅ B) (f : B ≅ D) (g : A ≅ D)
    (h : (a ≪≫ e ≪≫ b.symm) ≪≫ (b ≪≫ f ≪≫ d.symm) = a ≪≫ g ≪≫ d.symm) :
    e ≪≫ f = g := by
  apply isoConjugation_injective a d
  simpa only [Iso.trans_assoc, Iso.symm_self_id_assoc] using h

theorem isoCocycle_of_comparisons {C : Type v} [Category.{w} C]
    {A B D : C} {e e' : A ≅ B} {f f' : B ≅ D} {g g' : A ≅ D}
    (he : e = e') (hf : f = f') (hg : g = g') (h : e' ≪≫ f' = g') :
    e ≪≫ f = g := by
  rw [he, hf, hg]
  exact h

theorem isoConjugatedFunctorCocycle
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (K : C ⥤ D) {A B E : C} {A' B' E' : D}
    (a : A' ≅ K.obj A) (b : B' ≅ K.obj B) (c : E' ≅ K.obj E)
    (e : A ≅ B) (f : B ≅ E) (g : A ≅ E) (h : e ≪≫ f = g) :
    (a ≪≫ K.mapIso e ≪≫ b.symm) ≪≫ (b ≪≫ K.mapIso f ≪≫ c.symm) =
      a ≪≫ K.mapIso g ≪≫ c.symm := by
  rw [← h, Functor.mapIso_trans]
  simp only [Iso.trans_assoc, Iso.symm_self_id_assoc]

theorem overIso_eq_of_noetherianAffinePullbacks
    {S : Scheme.{u}} [IsLocallyNoetherian S] {A B : Over S} (e f : A ≅ B)
    (h : ∀ (C : CommRingCat.{u}) [IsNoetherianRing C] (a : Spec C ⟶ S),
      (Over.pullback a).mapIso e = (Over.pullback a).mapIso f) : e = f := by
  apply Iso.ext
  apply HilbertConstruction.Over.HomOpenCoverDetection.overHom_eq_of_openCoverPullbacks S.affineOpenCover.openCover
  intro i
  change S.affineOpenCover.I₀ at i
  exact congrArg Iso.hom (h (S.affineOpenCover.X i) (S.affineOpenCover.f i))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.IsoCocycleDetection.AffineIsoCocycleDetection
