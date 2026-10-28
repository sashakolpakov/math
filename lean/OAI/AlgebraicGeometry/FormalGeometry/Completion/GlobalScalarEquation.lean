import OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.BaseAlgebraPoints
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Global Scalar Equation -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.GlobalScalarEquation

noncomputable section

/-! A global function's equation u = 1 cuts out a closed subscheme,
with its scheme-theoretic factorization property for all test schemes. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

namespace Construction

universe u

def ringQuotientMap (R : CommRingCat.{u}) (I : Ideal R) : R ⟶ CommRingCat.of (R ⧸ I) :=
  CommRingCat.ofHom (Ideal.Quotient.mk I)

theorem globalRingPointEquiv_factorsQuotient (T : Scheme.{u}) (R : CommRingCat.{u})
    (I : Ideal R) (f : T ⟶ Spec R) :
    (∃ q : T ⟶ Spec (CommRingCat.of (R ⧸ I)), q ≫ Spec.map (ringQuotientMap R I) = f) ↔
      I ≤ RingHom.ker (Affine.BaseAlgebraPoints.Construction.globalRingPointEquiv T R f) := by
  constructor
  · rintro ⟨q, rfl⟩ a ha
    rw [Affine.BaseAlgebraPoints.Construction.globalRingPointEquiv_target]
    change Affine.BaseAlgebraPoints.Construction.globalRingPointEquiv T (CommRingCat.of (R ⧸ I)) q (Ideal.Quotient.mk I a) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
  · intro h
    let φ := Ideal.Quotient.lift I (Affine.BaseAlgebraPoints.Construction.globalRingPointEquiv T R f) h
    refine ⟨(Affine.BaseAlgebraPoints.Construction.globalRingPointEquiv T (CommRingCat.of (R ⧸ I))).symm φ, ?_⟩
    apply (Affine.BaseAlgebraPoints.Construction.globalRingPointEquiv T R).injective
    rw [Affine.BaseAlgebraPoints.Construction.globalRingPointEquiv_target, Equiv.apply_symm_apply]
    exact Ideal.Quotient.lift_comp_mk I (Affine.BaseAlgebraPoints.Construction.globalRingPointEquiv T R f) h

def scalarEqOneIdeal (X : Scheme.{u}) (a : Γ(X, ⊤)) : Ideal Γ(X, ⊤) := Ideal.span {a - 1}

def scalarEqOneScheme (X : Scheme.{u}) (a : Γ(X, ⊤)) : Over X :=
  Over.mk (pullback.fst X.toSpecΓ (Spec.map (ringQuotientMap Γ(X, ⊤) (scalarEqOneIdeal X a))))

instance scalarEqOneScheme_isClosedImmersion (X : Scheme.{u}) (a : Γ(X, ⊤)) :
    IsClosedImmersion (scalarEqOneScheme X a).hom := by
  have : IsClosedImmersion (Spec.map (ringQuotientMap Γ(X, ⊤) (scalarEqOneIdeal X a))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  change IsClosedImmersion (pullback.fst X.toSpecΓ (Spec.map (ringQuotientMap Γ(X, ⊤) (scalarEqOneIdeal X a))))
  infer_instance

theorem scalarEqOneScheme_hasLift_iff {X T : Scheme.{u}} (a : Γ(X, ⊤)) (t : T ⟶ X) :
    Nonempty (Over.mk t ⟶ scalarEqOneScheme X a) ↔ t.appTop a = 1 := by
  let q := Spec.map (ringQuotientMap Γ(X, ⊤) (scalarEqOneIdeal X a))
  have hf : Nonempty (Over.mk t ⟶ scalarEqOneScheme X a) ↔
      ∃ b : T ⟶ Spec (CommRingCat.of (Γ(X, ⊤) ⧸ scalarEqOneIdeal X a)), b ≫ q = t ≫ X.toSpecΓ := by
    constructor
    · rintro ⟨p⟩
      refine ⟨p.left ≫ pullback.snd X.toSpecΓ q, ?_⟩
      rw [Category.assoc, ← pullback.condition, ← Category.assoc]
      exact congrArg (fun z : T ⟶ X => z ≫ X.toSpecΓ) p.w
    · rintro ⟨b, hb⟩
      exact ⟨Over.homMk (pullback.lift t b hb.symm) (pullback.lift_fst _ _ _)⟩
  rw [hf, globalRingPointEquiv_factorsQuotient, Affine.BaseAlgebraPoints.Construction.globalRingPointEquiv_source,
    Affine.BaseAlgebraPoints.Construction.globalRingPointEquiv_toSpecΓ, RingHom.comp_id]
  change Ideal.span {a - 1} ≤ RingHom.ker t.appTop.hom ↔ _
  rw [Ideal.span_le, Set.singleton_subset_iff]
  change t.appTop.hom (a - 1) = 0 ↔ t.appTop.hom a = 1
  rw [map_sub, map_one, sub_eq_zero]

theorem scalarEqOneScheme_lift_unique {X T : Scheme.{u}} (a : Γ(X, ⊤)) (t : T ⟶ X)
    (p q : Over.mk t ⟶ scalarEqOneScheme X a) : p = q := by
  apply Over.OverMorphism.ext
  apply (cancel_mono (scalarEqOneScheme X a).hom).mp
  exact p.w.trans q.w.symm

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.GlobalScalarEquation
