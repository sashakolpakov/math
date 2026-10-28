import OAI.AlgebraicGeometry.Picard.Homomorphisms.SmoothChart

/-! # Change Base -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.ChangeBase.Construction

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.CategoryTheory.Limits

universe u

variable (p : ℕ) (hp : p.Prime)

set_option backward.isDefEq.respectTransparency.types false in
theorem frobeniusTwist_etaleBase_isPullback {U S : Scheme.{u}}
    (hS : (p : Γ(S, ⊤)) = 0) (j : U ⟶ S) [Etale j] (A : Over U) :
    IsPullback
      (pullback.fst A.hom (Frobenius.Construction.absoluteFrobenius p hp U (Frobenius.Construction.prime_eq_zero_of_map p hS j)))
      (pullback.snd A.hom (Frobenius.Construction.absoluteFrobenius p hp U (Frobenius.Construction.prime_eq_zero_of_map p hS j)) ≫ j)
      (A.hom ≫ j) (Frobenius.Construction.absoluteFrobenius p hp S hS) :=
  (IsPullback.of_hasPullback A.hom
    (Frobenius.Construction.absoluteFrobenius p hp U (Frobenius.Construction.prime_eq_zero_of_map p hS j))).paste_vert
      (Homomorphisms.Etale.Construction.absoluteFrobenius_square_isPullback_of_etale p hp hS j)

set_option backward.isDefEq.respectTransparency.types false in
theorem relativeFrobenius_etaleBase_factorization {U S : Scheme.{u}}
    (hS : (p : Γ(S, ⊤)) = 0) (j : U ⟶ S) [Etale j] (A : Over U) :
    (Frobenius.Construction.relativeFrobenius p hp hS (Over.mk (A.hom ≫ j))).left =
      (Frobenius.Construction.relativeFrobenius p hp (Frobenius.Construction.prime_eq_zero_of_map p hS j) A).left ≫
        (frobeniusTwist_etaleBase_isPullback p hp hS j A).isoPullback.hom := by
  apply pullback.hom_ext
  · erw [Frobenius.Construction.relativeFrobenius_comp_fst, Category.assoc, IsPullback.isoPullback_hom_fst,
      Frobenius.Construction.relativeFrobenius_comp_fst]
    rfl
  · let AS : Over S := Over.mk (A.hom ≫ j)
    let FU := (Frobenius.Construction.relativeFrobenius p hp (Frobenius.Construction.prime_eq_zero_of_map p hS j) A).left
    let FS := (Frobenius.Construction.relativeFrobenius p hp hS AS).left
    let πU := pullback.snd A.hom (Frobenius.Construction.absoluteFrobenius p hp U (Frobenius.Construction.prime_eq_zero_of_map p hS j))
    let πS := pullback.snd AS.hom (Frobenius.Construction.absoluteFrobenius p hp S hS)
    let i := (frobeniusTwist_etaleBase_isPullback p hp hS j A).isoPullback.hom
    have hFU : FU ≫ πU = A.hom := (Frobenius.Construction.relativeFrobenius p hp (Frobenius.Construction.prime_eq_zero_of_map p hS j) A).w
    have hFS : FS ≫ πS = A.hom ≫ j := (Frobenius.Construction.relativeFrobenius p hp hS AS).w
    have hi : i ≫ πS = πU ≫ j :=
      (frobeniusTwist_etaleBase_isPullback p hp hS j A).isoPullback_hom_snd
    calc
      FS ≫ πS = A.hom ≫ j := hFS
      _ = (FU ≫ πU) ≫ j := congrArg (fun t => t ≫ j) hFU.symm
      _ = FU ≫ (πU ≫ j) := Category.assoc FU πU j
      _ = FU ≫ (i ≫ πS) := congrArg (fun t => FU ≫ t) hi.symm
      _ = (FU ≫ i) ≫ πS := (Category.assoc FU i πS).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- Flatness is unchanged when an étale intermediate base is forgotten. -/
theorem relativeFrobenius_flat_under_etaleBase {U S : Scheme.{u}}
    (hS : (p : Γ(S, ⊤)) = 0) (j : U ⟶ S) [Etale j] (A : Over U)
    [hflat : Flat (Frobenius.Construction.relativeFrobenius p hp (Frobenius.Construction.prime_eq_zero_of_map p hS j) A).left] :
    Flat (Frobenius.Construction.relativeFrobenius p hp hS (Over.mk (A.hom ≫ j))).left := by
  rw [relativeFrobenius_etaleBase_factorization p hp hS j A]
  exact MorphismProperty.comp_mem @Flat _ _ hflat inferInstance

end OAI.AlgebraicGeometry.Picard.Homomorphisms.ChangeBase.Construction
