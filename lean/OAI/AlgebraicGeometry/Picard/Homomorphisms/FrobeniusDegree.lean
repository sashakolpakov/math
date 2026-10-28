import OAI.AlgebraicGeometry.Picard.Homomorphisms.SmoothFrobeniusRank

/-! # Frobenius Degree -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.FrobeniusDegree

noncomputable section

/-! Relative Frobenius of a smooth d-dimensional scheme has degree p^d. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

theorem relativeFrobenius_smooth_finrank
    (p : ℕ) (hp : p.Prime) {S : Scheme.{u}} (hS : (p : Γ(S, ⊤)) = 0)
    (A : Over S) (d : ℕ) [SmoothOfRelativeDimension d A.hom]
    (y : (Frobenius.Construction.frobeniusTwist p hp hS A).left) :
    (Frobenius.Construction.relativeFrobenius p hp hS A).left.finrank y = p ^ d := by
  have : Smooth A.hom := SmoothOfRelativeDimension.smooth d A.hom
  have : Flat (Frobenius.Construction.relativeFrobenius p hp hS A).left := Homomorphisms.Smooth.Construction.relativeFrobenius_smooth_flat p hp hS A
  obtain ⟨x, hxy⟩ := (Frobenius.Construction.relativeFrobenius p hp hS A).left.surjective y
  obtain ⟨U, hU, V, hV, hxV, e, hstd⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := d) (f := A.hom) x
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  let g := A.hom.resLE U V e
  have hg : g.appTop.hom.IsStandardSmoothOfRelativeDimension d :=
    (RingHom.isStandardSmoothOfRelativeDimension_respectsIso.arrow_mk_iso_iff
      (arrowResLEAppIso A.hom U V e)).mpr hstd
  have : LocallyOfFiniteType g := by
    rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)]
    exact SmoothFrobeniusRank.Construction.standardSmoothDimension_finiteType g.appTop.hom d hg
  let hUchar := Frobenius.Construction.prime_eq_zero_of_map p hS U.ι
  have : Flat (Frobenius.Construction.relativeFrobenius p hp hUchar (Over.mk g)).left :=
    Homomorphisms.Smooth.Construction.relativeFrobenius_affine_standardSmooth_flat p hp hUchar g (hg.isStandardSmooth _)
  have : LocallyOfFiniteType (Over.mk g).hom := inferInstanceAs (LocallyOfFiniteType g)
  have : IsFinite (Frobenius.Construction.relativeFrobenius p hp hUchar (Over.mk g)).left :=
    Properties.Construction.relativeFrobenius_finite p hp hUchar (Over.mk g)
  have hrU (z : (Frobenius.Construction.frobeniusTwist p hp hUchar (Over.mk g)).left) :
      (Frobenius.Construction.relativeFrobenius p hp hUchar (Over.mk g)).left.finrank z = p ^ d :=
    SmoothFrobeniusRank.Construction.relativeFrobenius_affine_standardSmooth_finrank p hp hUchar g d hg z
  let VA : Over S := Over.mk (V.ι ≫ A.hom)
  have hrVA (z : (Frobenius.Construction.frobeniusTwist p hp hS VA).left) :
      (Frobenius.Construction.relativeFrobenius p hp hS VA).left.finrank z = p ^ d := by
    have hbase := SmoothFrobeniusRank.Construction.relativeFrobenius_finrank_under_etaleBase p hp hS U.ι (Over.mk g) (p ^ d) hrU
    have heq : g ≫ U.ι = V.ι ≫ A.hom := Scheme.Hom.resLE_comp_ι A.hom e
    exact (heq ▸ hbase) z
  let i : VA ⟶ A := Over.homMk V.ι rfl
  have : Etale i.left := inferInstanceAs (Etale V.ι)
  let xV : V.toScheme := ⟨x, hxV⟩
  let yV := (Frobenius.Construction.relativeFrobenius p hp hS VA).left xV
  have hiy : ((Over.pullback (Frobenius.Construction.absoluteFrobenius p hp S hS)).map i).left yV = y := by
    have h := congrArg (fun q : VA ⟶ Frobenius.Construction.frobeniusTwist p hp hS A => q.left xV)
      ((Group.Construction.relativeFrobeniusNat p hp hS).naturality i)
    exact h.symm.trans hxy
  have h := (SmoothFrobeniusRank.Construction.relativeFrobenius_finrank_of_etale p hp hS i yV).symm.trans (hrVA yV)
  rw [hiy] at h
  exact h

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.FrobeniusDegree
