import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.GroupDivision
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.TorsionDetection

/-! # Endomorphism Divisibility -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Over a field, the endomorphisms acting as zero on full-level torsion are exactly the integer multiples of the level. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {K : Type u} [Field K] {g n : ℕ}
variable (A : Abelian.Schemes.AbelianScheme g (Spec (.of K)))

theorem Abelian.Schemes.AbelianScheme.fullLevel_endomorphism_divisibility (level : A.FullLevel n) (f : A.EndRing) :
    A.endRingTorsionAction n (Over.mk (𝟙 (Spec (.of K)))) f = 0 ↔
      ∃ d : A.EndRing, n • d = f := by
  constructor
  · intro h
    have hm := A.torsionMap_eq_of_baseAction level f 0
      (h.trans (A.endRingTorsionAction n (Over.mk (𝟙 (Spec (.of K))))).map_zero.symm)
    have hi := congrArg (fun a : A.torsionScheme n ⟶ A.torsionScheme n =>
      a ≫ A.torsionInclusion n) hm
    rw [Abelian.Schemes.AbelianScheme.torsionMap_comp_inclusion, Abelian.Schemes.AbelianScheme.torsionMap_comp_inclusion] at hi
    have hz : A.torsionInclusion n ≫ f.toMul.hom.hom = 1 :=
      hi.trans (MonObj.comp_one (A.torsionInclusion n))
    obtain ⟨d, hd, _⟩ := A.fullLevel_existsUnique_groupDivision A level f.toMul.hom.hom hz
    have : IsMonHom d.val := d.property
    let v : A.EndRing := Additive.ofMul (Grp.homMk d.val)
    have hv : v * (n : A.EndRing) = f := by
      have he : (v * (n : A.EndRing)).toMul.hom.hom = f.toMul.hom.hom :=
        (congrArg (fun a : A.scheme ⟶ A.scheme => a ≫ d.val) (A.endRing_natCast_hom n)).trans hd
      exact congrArg Additive.ofMul (Grp.hom_ext _ _ he)
    refine ⟨v, ?_⟩
    rw [nsmul_eq_mul, (Nat.cast_commute n v).eq]
    exact hv
  · rintro ⟨d, rfl⟩
    rw [nsmul_eq_mul, map_mul, A.endRingTorsionAction_natCast_self, zero_mul]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
