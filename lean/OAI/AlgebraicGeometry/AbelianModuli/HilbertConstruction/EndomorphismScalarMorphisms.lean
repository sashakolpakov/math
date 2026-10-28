import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EndomorphismScalars
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.PreservingUnits

/-! # Endomorphism Scalar Morphisms -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Additive scalar multiples and polarized automorphism differences in the actual endomorphism ring have their expected underlying scheme morphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}

theorem Abelian.Schemes.AbelianScheme.endRing_nsmul_hom (A : Abelian.Schemes.AbelianScheme g S) (d : A.EndRing) (n : ℕ) :
    (n • d).toMul.hom.hom = d.toMul.hom.hom ≫ A.multiplication n := by
  rw [nsmul_eq_mul, A.endRing_mul_toMul]
  change d.toMul.hom.hom ≫ (n : A.EndRing).toMul.hom.hom = _
  rw [A.endRing_natCast_hom]

theorem Moduli.Isomorphisms.LevelPreservingIso.endRing_difference_hom
    {A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S} (e : Moduli.Isomorphisms.LevelPreservingIso A A) :
    (e.endRingUnit.val - 1).toMul.hom.hom = e.abelian.hom * (𝟙 A.abelian.scheme)⁻¹ := by
  change (e.endRingUnit.val.toMul / (1 : A.abelian.EndRing).toMul).hom.hom = _
  rw [div_eq_mul_inv, Grp.Hom.hom_mul, Mon.Hom.hom_mul]
  rfl

theorem Moduli.Isomorphisms.LevelPreservingIso.difference_factor_of_nsmul
    {A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S} (e : Moduli.Isomorphisms.LevelPreservingIso A A)
    (n : ℕ) (d : A.abelian.EndRing) (hd : n • d = e.endRingUnit.val - 1) :
    d.toMul.hom.hom ≫ A.abelian.multiplication n = e.abelian.hom * (𝟙 A.abelian.scheme)⁻¹ :=
  (A.abelian.endRing_nsmul_hom d n).symm.trans
    ((congrArg (fun a : A.abelian.EndRing => a.toMul.hom.hom) hd).trans e.endRing_difference_hom)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
