import OAI.AlgebraicGeometry.Picard.Homomorphisms.ChangeBase
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.RingHom.StandardSmooth

/-! # Smooth -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.Smooth.Construction

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.CategoryTheory.Limits

universe u

variable (p : ℕ) (hp : p.Prime)

set_option backward.isDefEq.respectTransparency.types false in
theorem relativeFrobenius_standardSmooth_flat (R T : Type u) [CommRing R] [CommRing T]
    (hR : (p : R) = 0) (f : R →+* T) (hf : f.IsStandardSmooth) :
    Flat (Frobenius.Construction.relativeFrobenius p hp (Affine.Construction.prime_eq_zero_spec p R hR)
      (Over.mk (Spec.map (CommRingCat.ofHom f)))).left := by
  obtain ⟨n, g, hg, hge⟩ := hf.exists_etale_mvPolynomial
  let A := Over.mk (Spec.map (CommRingCat.ofHom f))
  let B := Over.mk (Spec.map (CommRingCat.ofHom
    (MvPolynomial.C : R →+* MvPolynomial (Fin n) R)))
  let e : A ⟶ B := Over.homMk (Spec.map (CommRingCat.ofHom g)) (by
    change Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C) = _
    rw [← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext hg))
  have : Etale e.left := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr hge
  have : Flat (Frobenius.Construction.relativeFrobenius p hp (Affine.Construction.prime_eq_zero_spec p R hR) B).left :=
    Affine.Construction.relativeFrobenius_polynomial_flat p hp R hR (Fin n)
  exact SmoothChart.Construction.relativeFrobenius_flat_of_etale p hp (Affine.Construction.prime_eq_zero_spec p R hR) e

set_option backward.isDefEq.respectTransparency.types false in
theorem relativeFrobenius_affine_standardSmooth_flat {X Y : Scheme.{u}}
    [IsAffine X] [IsAffine Y] (hY : (p : Γ(Y, ⊤)) = 0) (f : X ⟶ Y)
    (hf : f.appTop.hom.IsStandardSmooth) :
    Flat (Frobenius.Construction.relativeFrobenius p hp hY (Over.mk f)).left := by
  let A : Over (Spec Γ(Y, ⊤)) := Over.mk (f ≫ Y.isoSpec.hom)
  let B : Over (Spec Γ(Y, ⊤)) := Over.mk (Spec.map f.appTop)
  let e : A ⟶ B := Over.homMk X.isoSpec.hom (Scheme.isoSpec_hom_naturality f)
  have : Etale e.left := inferInstanceAs (Etale X.isoSpec.hom)
  have hSpec : (p : Γ(Spec Γ(Y, ⊤), ⊤)) = 0 := Affine.Construction.prime_eq_zero_spec p Γ(Y, ⊤) hY
  have : Flat (Frobenius.Construction.relativeFrobenius p hp hSpec B).left :=
    relativeFrobenius_standardSmooth_flat p hp Γ(Y, ⊤) Γ(X, ⊤) hY f.appTop.hom hf
  have hA : Flat (Frobenius.Construction.relativeFrobenius p hp hSpec A).left :=
    SmoothChart.Construction.relativeFrobenius_flat_of_etale p hp hSpec e
  have hbase := ChangeBase.Construction.relativeFrobenius_flat_under_etaleBase p hp hY Y.isoSpec.inv A
  change Flat (Frobenius.Construction.relativeFrobenius p hp hY
    (Over.mk ((f ≫ Y.isoSpec.hom) ≫ Y.isoSpec.inv))).left at hbase
  have heq : (f ≫ Y.isoSpec.hom) ≫ Y.isoSpec.inv = f :=
    (Category.assoc f _ _).trans
      ((congrArg (fun t => f ≫ t) Y.isoSpec.hom_inv_id).trans (Category.comp_id f))
  exact heq ▸ hbase

set_option backward.isDefEq.respectTransparency.types false in
/-- Flatness of relative Frobenius for a smooth scheme, proved on standard
smooth affine charts and transferred back through the actual base changes. -/
theorem relativeFrobenius_smooth_flat {S : Scheme.{u}}
    (hS : (p : Γ(S, ⊤)) = 0) (A : Over S) [Smooth A.hom] :
    Flat (Frobenius.Construction.relativeFrobenius p hp hS A).left := by
  have hlocal : ∀ x : A.left, ∃ V : A.left.Opens,
      x ∈ V ∧ Flat (V.ι ≫ (Frobenius.Construction.relativeFrobenius p hp hS A).left) := by
    intro x
    obtain ⟨U, hU, V, hV, hxV, e, hstd⟩ := Smooth.exists_isStandardSmooth A.hom x
    have : IsAffine U.toScheme := hU
    have : IsAffine V.toScheme := hV
    let g := A.hom.resLE U V e
    have hg : g.appTop.hom.IsStandardSmooth :=
      (RingHom.isStandardSmooth_respectsIso.arrow_mk_iso_iff
        (arrowResLEAppIso A.hom U V e)).mpr hstd
    have hUchar := Frobenius.Construction.prime_eq_zero_of_map p hS U.ι
    have : Flat (Frobenius.Construction.relativeFrobenius p hp hUchar (Over.mk g)).left :=
      relativeFrobenius_affine_standardSmooth_flat p hp hUchar g hg
    have hbase := ChangeBase.Construction.relativeFrobenius_flat_under_etaleBase p hp hS U.ι (Over.mk g)
    change Flat (Frobenius.Construction.relativeFrobenius p hp hS (Over.mk (g ≫ U.ι))).left at hbase
    let VA : Over S := Over.mk (V.ι ≫ A.hom)
    have hVA : Flat (Frobenius.Construction.relativeFrobenius p hp hS VA).left := by
      change Flat (Frobenius.Construction.relativeFrobenius p hp hS (Over.mk (V.ι ≫ A.hom))).left
      have heq : g ≫ U.ι = V.ι ≫ A.hom := Scheme.Hom.resLE_comp_ι A.hom e
      exact heq ▸ hbase
    let i : VA ⟶ A := Over.homMk V.ι rfl
    have hi : Flat i.left := inferInstanceAs (Flat V.ι)
    have htwist : Flat ((Over.pullback (Frobenius.Construction.absoluteFrobenius p hp S hS)).map i).left :=
      MorphismProperty.of_isPullback (P := @Flat)
        (SmoothChart.Construction.frobeniusTwist_map_isPullback p hp hS i) hi
    have hcomp := MorphismProperty.comp_mem @Flat _ _ hVA htwist
    have hnat := congrArg Over.Hom.left ((Group.Construction.relativeFrobeniusNat p hp hS).naturality i)
    have hnat' : V.ι ≫ (Frobenius.Construction.relativeFrobenius p hp hS A).left =
        (Frobenius.Construction.relativeFrobenius p hp hS VA).left ≫
          ((Over.pullback (Frobenius.Construction.absoluteFrobenius p hp S hS)).map i).left := hnat
    refine ⟨V, hxV, ?_⟩
    exact hnat'.symm ▸ hcomp
  choose V hmem hflat using hlocal
  apply IsZariskiLocalAtSource.of_iSup_eq_top (P := @Flat) V _ hflat
  apply top_unique
  intro x _
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hmem x⟩

end OAI.AlgebraicGeometry.Picard.Homomorphisms.Smooth.Construction
