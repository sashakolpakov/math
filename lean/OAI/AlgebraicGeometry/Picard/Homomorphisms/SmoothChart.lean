import OAI.AlgebraicGeometry.Picard.Homomorphisms.Affine
import OAI.AlgebraicGeometry.Picard.Homomorphisms.Group

/-! # Smooth Chart -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.SmoothChart.Construction

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.CategoryTheory.Limits

universe u

variable (p : ℕ) (hp : p.Prime)

set_option backward.isDefEq.respectTransparency.types false in
theorem frobeniusTwist_map_isPullback {S : Scheme.{u}}
    (hS : (p : Γ(S, ⊤)) = 0) {A B : Over S} (f : A ⟶ B) :
    IsPullback
      (pullback.fst A.hom (Frobenius.Construction.absoluteFrobenius p hp S hS))
      ((Over.pullback (Frobenius.Construction.absoluteFrobenius p hp S hS)).map f).left
      f.left (pullback.fst B.hom (Frobenius.Construction.absoluteFrobenius p hp S hS)) := by
  let F := Frobenius.Construction.absoluteFrobenius p hp S hS
  let f' := ((Over.pullback F).map f).left
  have hfst : pullback.fst A.hom F ≫ f.left = f' ≫ pullback.fst B.hom F := by
    exact (pullback.lift_fst _ _ _).symm
  have hsnd : f' ≫ pullback.snd B.hom F = pullback.snd A.hom F := by
    exact ((Over.pullback F).map f).w
  have hout : IsPullback (pullback.fst A.hom F)
      (f' ≫ pullback.snd B.hom F) (f.left ≫ B.hom) F := by
    rw [hsnd, f.w]
    exact IsPullback.of_hasPullback A.hom F
  exact hout.of_bot hfst (IsPullback.of_hasPullback B.hom F)

set_option backward.isDefEq.respectTransparency.types false in
/-- Relative Frobenius commutes with an étale change of source. -/
theorem relativeFrobenius_square_isPullback_of_etale {S : Scheme.{u}}
    (hS : (p : Γ(S, ⊤)) = 0) {A B : Over S} (f : A ⟶ B) [Etale f.left] :
    IsPullback (Frobenius.Construction.relativeFrobenius p hp hS A).left f.left
      ((Over.pullback (Frobenius.Construction.absoluteFrobenius p hp S hS)).map f).left
      (Frobenius.Construction.relativeFrobenius p hp hS B).left := by
  have hout : IsPullback
      ((Frobenius.Construction.relativeFrobenius p hp hS A).left ≫
        pullback.fst A.hom (Frobenius.Construction.absoluteFrobenius p hp S hS))
      f.left f.left
      ((Frobenius.Construction.relativeFrobenius p hp hS B).left ≫
        pullback.fst B.hom (Frobenius.Construction.absoluteFrobenius p hp S hS)) := by
    erw [Frobenius.Construction.relativeFrobenius_comp_fst, Frobenius.Construction.relativeFrobenius_comp_fst]
    exact Homomorphisms.Etale.Construction.absoluteFrobenius_square_isPullback_of_etale p hp
      (Frobenius.Construction.prime_eq_zero_of_map p hS B.hom) f.left
  have hcomm := congrArg Over.Hom.left ((Group.Construction.relativeFrobeniusNat p hp hS).naturality f)
  exact hout.of_right hcomm.symm (frobeniusTwist_map_isPullback p hp hS f)

set_option backward.isDefEq.respectTransparency.types false in
/-- Flatness of relative Frobenius transfers to an étale chart. -/
theorem relativeFrobenius_flat_of_etale {S : Scheme.{u}}
    (hS : (p : Γ(S, ⊤)) = 0) {A B : Over S} (f : A ⟶ B) [Etale f.left]
    [hflat : Flat (Frobenius.Construction.relativeFrobenius p hp hS B).left] :
    Flat (Frobenius.Construction.relativeFrobenius p hp hS A).left :=
  MorphismProperty.of_isPullback (P := @Flat)
    (relativeFrobenius_square_isPullback_of_etale p hp hS f).flip hflat

end OAI.AlgebraicGeometry.Picard.Homomorphisms.SmoothChart.Construction
