import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-! # Scalar -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Residue.Scalar

noncomputable section

/-! Maps between residue-field vector spaces that are linear over the base ring are automatically linear over the residue field. -/
open _root_.CategoryTheory
universe u

def fractionGeneratedLinearMap {R K : Type u} [CommRing R] [Field K]
    (f : R →+* K) (hf : ∀ t : K, ∃ a b : R, f b ≠ 0 ∧ t * f b = f a)
    {M Q : ModuleCat.{u} K}
    (α : (ModuleCat.restrictScalars.{u} f).obj M ⟶ (ModuleCat.restrictScalars.{u} f).obj Q) : M ⟶ Q :=
  ModuleCat.ofHom
    { toFun := α
      map_add' := fun x y => α.hom.map_add x y
      map_smul' := by
        intro t x
        obtain ⟨a, b, hb, ht⟩ := hf t
        have hinj : Function.Injective (fun y : Q => f b • y) := by
          intro y z hyz
          have he := congrArg (fun v : Q => (f b)⁻¹ • v) hyz
          simpa only [smul_smul, inv_mul_cancel₀ hb, one_smul] using he
        apply hinj
        have hbt : f b * t = f a := (mul_comm (f b) t).trans ht
        calc
          f b • α (t • x) = α (f b • (t • x)) := (α.hom.map_smul b (t • x)).symm
          _ = α (f a • x) := congrArg α (by rw [smul_smul, hbt])
          _ = f a • α x := α.hom.map_smul a x
          _ = f b • (t • α x) := by rw [smul_smul, hbt] }

theorem restrictScalars_full_of_fractionGenerated {R K : Type u} [CommRing R] [Field K]
    (f : R →+* K) (hf : ∀ t : K, ∃ a b : R, f b ≠ 0 ∧ t * f b = f a) :
    (ModuleCat.restrictScalars.{u} f).Full where
  map_surjective α := ⟨fractionGeneratedLinearMap f hf α, rfl⟩

theorem residueField_fractionGenerated {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime] :
    ∀ t : p.ResidueField, ∃ a b : R,
      algebraMap R p.ResidueField b ≠ 0 ∧ t * algebraMap R p.ResidueField b = algebraMap R p.ResidueField a := by
  intro t
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors (R ⧸ p)) t
  obtain ⟨a₀, ha⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b₀, hb⟩ := Ideal.Quotient.mk_surjective b.val
  have ha' : algebraMap (R ⧸ p) p.ResidueField a = algebraMap R p.ResidueField a₀ := by rw [← ha]; rfl
  have hb' : algebraMap (R ⧸ p) p.ResidueField b.val = algebraMap R p.ResidueField b₀ := by rw [← hb]; rfl
  have hbK : algebraMap (R ⧸ p) p.ResidueField b.val ≠ 0 := (IsLocalization.map_units p.ResidueField b).ne_zero
  refine ⟨a₀, b₀, hb'.symm ▸ hbK, ?_⟩
  exact (congrArg (fun v => t * v) hb').symm.trans (hab.trans ha')

theorem residueField_restrictScalars_full {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime] :
    (ModuleCat.restrictScalars.{u} (algebraMap R p.ResidueField)).Full :=
  restrictScalars_full_of_fractionGenerated (algebraMap R p.ResidueField) (residueField_fractionGenerated p)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Residue.Scalar
