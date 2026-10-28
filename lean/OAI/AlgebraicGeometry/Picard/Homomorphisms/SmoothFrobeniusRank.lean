import OAI.AlgebraicGeometry.Picard.Homomorphisms.AffineFrobeniusRank
import OAI.AlgebraicGeometry.Picard.Homomorphisms.Smooth

/-! # Smooth Frobenius Rank -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.SmoothFrobeniusRank

noncomputable section

/-! The rank of relative Frobenius on standard smooth charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable (p : ℕ) (hp : p.Prime)

theorem relativeFrobenius_finrank_of_etale {S : Scheme.{u}}
    (hS : (p : Γ(S, ⊤)) = 0) {A B : Over S} (f : A ⟶ B) [Etale f.left]
    [Flat (Frobenius.Construction.relativeFrobenius p hp hS B).left] [IsFinite (Frobenius.Construction.relativeFrobenius p hp hS B).left]
    (x : (Frobenius.Construction.frobeniusTwist p hp hS A).left) :
    (Frobenius.Construction.relativeFrobenius p hp hS A).left.finrank x =
      (Frobenius.Construction.relativeFrobenius p hp hS B).left.finrank
        (((Over.pullback (Frobenius.Construction.absoluteFrobenius p hp S hS)).map f).left x) :=
  Scheme.Hom.finrank_of_isPullback f.left (Frobenius.Construction.relativeFrobenius p hp hS A).left
    (Frobenius.Construction.relativeFrobenius p hp hS B).left ((Over.pullback (Frobenius.Construction.absoluteFrobenius p hp S hS)).map f).left
    (SmoothChart.Construction.relativeFrobenius_square_isPullback_of_etale p hp hS f).flip x

theorem relativeFrobenius_finrank_under_etaleBase {U S : Scheme.{u}}
    (hS : (p : Γ(S, ⊤)) = 0) (j : U ⟶ S) [Etale j] (A : Over U)
    [Flat (Frobenius.Construction.relativeFrobenius p hp (Frobenius.Construction.prime_eq_zero_of_map p hS j) A).left]
    [IsFinite (Frobenius.Construction.relativeFrobenius p hp (Frobenius.Construction.prime_eq_zero_of_map p hS j) A).left]
    (d : ℕ) (h : ∀ x, (Frobenius.Construction.relativeFrobenius p hp (Frobenius.Construction.prime_eq_zero_of_map p hS j) A).left.finrank x = d)
    (y : (Frobenius.Construction.frobeniusTwist p hp hS (Over.mk (A.hom ≫ j))).left) :
    (Frobenius.Construction.relativeFrobenius p hp hS (Over.mk (A.hom ≫ j))).left.finrank y = d := by
  rw [ChangeBase.Construction.relativeFrobenius_etaleBase_factorization p hp hS j A]
  erw [AffineFrobeniusRank.Construction.finrank_comp_targetIso]
  exact h _

theorem relativeFrobenius_standardSmooth_finrank (R T : Type u) [CommRing R] [CommRing T]
    (hR : (p : R) = 0) (f : R →+* T) (d : ℕ) (hf : f.IsStandardSmoothOfRelativeDimension d)
    (y : (Frobenius.Construction.frobeniusTwist p hp (Affine.Construction.prime_eq_zero_spec p R hR)
      (Over.mk (Spec.map (CommRingCat.ofHom f)))).left) :
    (Frobenius.Construction.relativeFrobenius p hp (Affine.Construction.prime_eq_zero_spec p R hR)
      (Over.mk (Spec.map (CommRingCat.ofHom f)))).left.finrank y = p ^ d := by
  obtain ⟨g, hg, hge⟩ := hf.exists_etale_mvPolynomial
  let A := Over.mk (Spec.map (CommRingCat.ofHom f))
  let B := Over.mk (Spec.map (CommRingCat.ofHom
    (MvPolynomial.C : R →+* MvPolynomial (Fin d) R)))
  let e : A ⟶ B := Over.homMk (Spec.map (CommRingCat.ofHom g)) (by
    change Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C) = _
    rw [← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext hg))
  have : Etale e.left := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr hge
  have : LocallyOfFiniteType B.hom := by
    change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial (Fin d) R)))
    apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  have : Flat (Frobenius.Construction.relativeFrobenius p hp (Affine.Construction.prime_eq_zero_spec p R hR) B).left :=
    Affine.Construction.relativeFrobenius_polynomial_flat p hp R hR (Fin d)
  rw [relativeFrobenius_finrank_of_etale p hp (Affine.Construction.prime_eq_zero_spec p R hR) e]
  simpa using AffineFrobeniusRank.Construction.relativeFrobenius_polynomial_finrank p hp R hR (Fin d)
    (((Over.pullback (Frobenius.Construction.absoluteFrobenius p hp _ (Affine.Construction.prime_eq_zero_spec p R hR))).map e).left y)

theorem standardSmoothDimension_finiteType {R T : Type u} [CommRing R] [CommRing T]
    (f : R →+* T) (d : ℕ) (hf : f.IsStandardSmoothOfRelativeDimension d) : f.FiniteType := by
  algebraize [f]
  have : Algebra.IsStandardSmoothOfRelativeDimension d R T := hf
  have : Algebra.IsStandardSmooth R T := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth d
  exact RingHom.finiteType_algebraMap.mpr inferInstance

theorem relativeFrobenius_affine_standardSmooth_finrank {X Y : Scheme.{u}}
    [IsAffine X] [IsAffine Y] (hY : (p : Γ(Y, ⊤)) = 0) (f : X ⟶ Y)
    (d : ℕ) (hf : f.appTop.hom.IsStandardSmoothOfRelativeDimension d)
    (y : (Frobenius.Construction.frobeniusTwist p hp hY (Over.mk f)).left) :
    (Frobenius.Construction.relativeFrobenius p hp hY (Over.mk f)).left.finrank y = p ^ d := by
  let A : Over (Spec Γ(Y, ⊤)) := Over.mk (f ≫ Y.isoSpec.hom)
  let B : Over (Spec Γ(Y, ⊤)) := Over.mk (Spec.map f.appTop)
  let e : A ⟶ B := Over.homMk X.isoSpec.hom (Scheme.isoSpec_hom_naturality f)
  have : Etale e.left := inferInstanceAs (Etale X.isoSpec.hom)
  have hSpec : (p : Γ(Spec Γ(Y, ⊤), ⊤)) = 0 := Affine.Construction.prime_eq_zero_spec p Γ(Y, ⊤) hY
  have : LocallyOfFiniteType B.hom := by
    change LocallyOfFiniteType (Spec.map f.appTop)
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (standardSmoothDimension_finiteType f.appTop.hom d hf)
  have hstd : f.appTop.hom.IsStandardSmooth := hf.isStandardSmooth _
  have : Flat (Frobenius.Construction.relativeFrobenius p hp hSpec B).left :=
    Smooth.Construction.relativeFrobenius_standardSmooth_flat p hp Γ(Y, ⊤) Γ(X, ⊤) hY f.appTop.hom hstd
  have : Flat (Frobenius.Construction.relativeFrobenius p hp hSpec A).left := SmoothChart.Construction.relativeFrobenius_flat_of_etale p hp hSpec e
  have : LocallyOfFiniteType A.hom := by
    have heq : e.left ≫ B.hom = A.hom := e.w
    rw [← heq]
    infer_instance
  have hr (x : (Frobenius.Construction.frobeniusTwist p hp hSpec A).left) :
      (Frobenius.Construction.relativeFrobenius p hp hSpec A).left.finrank x = p ^ d := by
    rw [relativeFrobenius_finrank_of_etale p hp hSpec e]
    exact relativeFrobenius_standardSmooth_finrank p hp Γ(Y, ⊤) Γ(X, ⊤) hY f.appTop.hom d hf _
  have hbase := relativeFrobenius_finrank_under_etaleBase p hp hY Y.isoSpec.inv A (p ^ d) hr
  change ∀ x, (Frobenius.Construction.relativeFrobenius p hp hY (Over.mk ((f ≫ Y.isoSpec.hom) ≫ Y.isoSpec.inv))).left.finrank x =
    p ^ d at hbase
  have heq : (f ≫ Y.isoSpec.hom) ≫ Y.isoSpec.inv = f := by simp
  exact (heq ▸ hbase) y

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.SmoothFrobeniusRank
