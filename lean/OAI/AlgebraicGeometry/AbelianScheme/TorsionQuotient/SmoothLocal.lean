import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.LocalSmooth
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.LocalLifts
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Smooth Local -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SmoothLocal.SmoothLocalLifting

/-!
# TorsionQuotient: local infinitesimal lifting for smooth schemes

Formal smoothness of the actual stalk map gives a lift of its local ring
homomorphism. The resulting local map is realized as a scheme morphism.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem formallySmooth_stalk {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] (x : X) :
    (f.stalkMap x).hom.FormallySmooth := by
  have hx : x ∈ f.smoothLocus := by rw [f.smoothLocus_eq_top]; trivial
  exact hx

theorem exists_stalk_lift {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] (x : X)
    {C B : CommRingCat.{u}} (p : C ⟶ B) (hp : Function.Surjective p)
    (hker : RingHom.ker p.hom ^ 2 = ⊥)
    (a : X.presheaf.stalk x ⟶ B) [IsLocalHom a.hom]
    (b : Y.presheaf.stalk (f x) ⟶ C)
    (hab : f.stalkMap x ≫ a = b ≫ p) :
    ∃ l : X.presheaf.stalk x ⟶ C,
      IsLocalHom l.hom ∧ l ≫ p = a ∧ f.stalkMap x ≫ l = b := by
  let R := Y.presheaf.stalk (f x)
  let A := X.presheaf.stalk x
  let : Algebra R A := (f.stalkMap x).hom.toAlgebra
  let : Algebra R C := b.hom.toAlgebra
  let : Algebra R B := (a.hom.comp (f.stalkMap x).hom).toAlgebra
  let : Algebra.FormallySmooth R A := formallySmooth_stalk f x
  let a' : A →ₐ[R] B := { a.hom with commutes' := fun _ => rfl }
  let p' : C →ₐ[R] B :=
    { p.hom with commutes' := fun r => (congrArg (fun z => z.hom r) hab).symm }
  let l := Algebra.FormallySmooth.liftOfSurjective a' p' hp ⟨2, hker⟩
  have hl : p'.comp l = a' :=
    Algebra.FormallySmooth.comp_liftOfSurjective a' p' hp ⟨2, hker⟩
  have hlp : p.hom.comp l.toRingHom = a.hom := congrArg AlgHom.toRingHom hl
  let : IsLocalHom (p.hom.comp l.toRingHom) := hlp.symm ▸ (inferInstance : IsLocalHom a.hom)
  let : IsLocalHom l.toRingHom := isLocalHom_of_comp l.toRingHom p.hom
  refine ⟨CommRingCat.ofHom l.toRingHom, inferInstance, ?_, ?_⟩
  · exact CommRingCat.hom_ext hlp
  · ext r
    exact l.commutes r

/-- Smooth scheme morphisms lift over a square-zero extension of local
test rings. Both the reduction and the prescribed base map are preserved. -/
theorem exists_scheme_lift {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f]
    {C B : CommRingCat.{u}} [IsLocalRing C] [IsLocalRing B]
    (p : C ⟶ B) (hp : Function.Surjective p) (hker : RingHom.ker p.hom ^ 2 = ⊥)
    (a : Spec B ⟶ X) (b : Spec C ⟶ Y) (hab : a ≫ f = Spec.map p ≫ b) :
    ∃ l : Spec C ⟶ X, Spec.map p ≫ l = a ∧ l ≫ f = b := by
  let : IsLocalHom p.hom := LocalSmooth.LocalSmoothCriterion.isLocalHom_of_surjective_squareZero p.hom hp hker
  obtain ⟨⟨x, ⟨α, hα⟩⟩, rfl⟩ := (SpecToEquivOfLocalRing X B).symm.surjective a
  obtain ⟨⟨y, ⟨β, hβ⟩⟩, rfl⟩ := (SpecToEquivOfLocalRing Y C).symm.surjective b
  let : IsLocalHom α.hom := hα
  let : IsLocalHom β.hom := hβ
  change (Spec.map α ≫ X.fromSpecStalk x) ≫ f =
    Spec.map p ≫ Spec.map β ≫ Y.fromSpecStalk y at hab
  let : IsLocalHom (f.stalkMap x ≫ α).hom := by
    change IsLocalHom (α.hom.comp (f.stalkMap x).hom)
    infer_instance
  let : IsLocalHom (β ≫ p).hom := by
    change IsLocalHom (p.hom.comp β.hom)
    infer_instance
  have he : (SpecToEquivOfLocalRing Y B).symm
      ⟨f x, ⟨f.stalkMap x ≫ α, inferInstance⟩⟩ =
      (SpecToEquivOfLocalRing Y B).symm ⟨y, ⟨β ≫ p, inferInstance⟩⟩ := by
    change LocalLifts.LocalSchemeLifts.ofGerm Y (f x) (f.stalkMap x ≫ α) =
      LocalLifts.LocalSchemeLifts.ofGerm Y y (β ≫ p)
    rw [LocalLifts.LocalSchemeLifts.ofGerm_comp]
    simpa only [LocalLifts.LocalSchemeLifts.ofGerm, Spec.map_comp, Category.assoc] using hab
  obtain ⟨hy, hmaps⟩ := SpecToEquivOfLocalRing_eq_iff.mp
    ((SpecToEquivOfLocalRing Y B).symm.injective he)
  change f x = y at hy
  subst y
  have hmaps' : f.stalkMap x ≫ α = β ≫ p := by simpa using hmaps
  obtain ⟨l, hl, hlp, hfl⟩ := exists_stalk_lift f x p hp hker α β hmaps'
  let : IsLocalHom l.hom := hl
  refine ⟨LocalLifts.LocalSchemeLifts.ofGerm X x l, ?_, ?_⟩
  · change Spec.map p ≫ Spec.map l ≫ X.fromSpecStalk x = _
    rw [← Spec.map_comp_assoc, hlp]
    rfl
  · rw [← LocalLifts.LocalSchemeLifts.ofGerm_comp, hfl]
    rfl

end OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SmoothLocal.SmoothLocalLifting
