import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.EffectiveDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LevelMultiplication.Isogeny

/-! # Torsion Annihilator Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Homomorphisms killing the full-level torsion descend uniquely through multiplication. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} {g h n : ℕ} (A : Abelian.Schemes.AbelianScheme g S) (B : Abelian.Schemes.AbelianScheme h S)

theorem Abelian.Schemes.AbelianScheme.torsion_annihilator_relation (m : A.scheme ⟶ B.scheme) [IsMonHom m]
    (hm : A.torsionInclusion n ≫ m = 1) {T : Over S} (a b : T ⟶ A.scheme)
    (hab : a ≫ A.multiplication n = b ≫ A.multiplication n) : a ≫ m = b ≫ m := by
  have hp : a ^ n = b ^ n := (A.comp_multiplication n a).symm.trans
    (hab.trans (A.comp_multiplication n b))
  let t : A.torsionPoints n T := ⟨b / a, by
    change (b / a) ^ n = 1
    rw [div_pow, div_eq_one]
    exact hp.symm⟩
  let e := (A.torsionSchemePointsEquiv n T).symm t
  have he : e ≫ A.torsionInclusion n = b / a :=
    congrArg (fun x : A.torsionPoints n T => x.val)
      ((A.torsionSchemePointsEquiv n T).apply_symm_apply t)
  have hz : (b / a) ≫ m = 1 := by
    calc
      (b / a) ≫ m = (e ≫ A.torsionInclusion n) ≫ m := congrArg (fun f => f ≫ m) he.symm
      _ = e ≫ (1 : A.torsionScheme n ⟶ B.scheme) :=
        (Category.assoc _ _ _).trans (congrArg (fun f => e ≫ f) hm)
      _ = 1 := MonObj.comp_one e
  exact (div_eq_one.mp ((GrpObj.div_comp b a m).symm.trans hz)).symm

theorem Abelian.Schemes.AbelianScheme.fullLevel_existsUnique_division (level : A.FullLevel n) (m : A.scheme ⟶ B.scheme)
    [IsMonHom m] (hm : A.torsionInclusion n ≫ m = 1) :
    ∃! d : A.scheme ⟶ B.scheme, A.multiplication n ≫ d = m := by
  have := A.fullLevel_multiplication_effectiveEpi level
  exact HilbertConstruction.Over.EffectiveDescent.over_existsUnique_factor_of_effectiveEpi (A.multiplication n) m
    (fun a b hab => A.torsion_annihilator_relation B m hm a b hab)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
