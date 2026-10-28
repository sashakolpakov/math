import OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedPolynomial.Universal
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Filtered.Final

/-! # Tower -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedPolynomial.Tower.FramedPolynomialTower

noncomputable section

/-!
# Terminal p-power levels and the final native framed tower

Each actual polynomial envelope level is terminal among framed crystalline
objects killed by its power of p. The levels form a final functor from
the natural numbers into the framed site. Thus the tower computes limits
of framed presheaves through its opposite, without a cofinality assumption.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Limits

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B]
  (r : MvPolynomial σ (WittVector p k) →+* B) (hr : Function.Surjective r)
  (hbase : r.comp (algebraMap (WittVector p k) (MvPolynomial σ (WittVector p k))) =
    (algebraMap k B).comp WittVector.constantCoeff)

local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.Category.FramedCrystallineCategory.Object p k B σ (fun i => r (MvPolynomial.X i))
local notation "L" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedPolynomial.Levels.FramedPolynomialLevels.level p k B σ r hr hbase

def bounded (n : ℕ) : ObjectProperty C := fun P => (p : P.base.thickening.ring) ^ (n + 1) = 0

def terminal (n : ℕ) : (bounded p k B σ r n).FullSubcategory :=
  ⟨L n, Affine.EnvelopeFrameUniversal.AffineEnvelopeFrameUniversal.p_pow_eq_zero p k B _ r hr hbase n⟩

def isTerminal (n : ℕ) : IsTerminal (terminal p k B σ r hr hbase n) :=
  IsTerminal.ofUniqueHom
    (fun P => ObjectProperty.homMk (Levels.FramedPolynomialLevels.map p k B σ r hr hbase P.obj n P.property))
    (fun P g => ObjectProperty.hom_ext (bounded p k B σ r n)
      (Universal.FramedPolynomialUniversal.unique p k B σ r hr hbase P.obj n P.property g.hom))

def transition {m n : ℕ} (h : m ≤ n) : L m ⟶ L n :=
  Levels.FramedPolynomialLevels.map p k B σ r hr hbase (L m) n
    (pow_eq_zero_of_le (Nat.add_le_add_right h 1) (Affine.EnvelopeFrameUniversal.AffineEnvelopeFrameUniversal.p_pow_eq_zero p k B _ r hr hbase m))

def tower : ℕ ⥤ C where
  obj := L
  map f := transition p k B σ r hr hbase (leOfHom f)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

theorem exists_map (P : FramedCrystalline.Category.FramedCrystallineCategory.Object p k B σ (fun i => r (MvPolynomial.X i))) :
    ∃ n : ℕ, Nonempty (P ⟶ (tower p k B σ r hr hbase).obj n) := by
  obtain ⟨n, hn⟩ := P.base.thickening.p_nilpotent
  refine ⟨n, ⟨Levels.FramedPolynomialLevels.map p k B σ r hr hbase P n ?_⟩⟩
  rw [pow_succ, hn, zero_mul]

instance final : (tower p k B σ r hr hbase).Final :=
  Functor.final_of_exists_of_isFiltered _ (exists_map p k B σ r hr hbase)
    (fun {P n} s s' => ⟨n, 𝟙 n,
      congrArg (fun g => g ≫ (tower p k B σ r hr hbase).map (𝟙 n))
        (@Subsingleton.elim (P ⟶ L n) (Universal.FramedPolynomialUniversal.hom_subsingleton p k B σ r hr hbase P n) s s')⟩)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedPolynomial.Tower.FramedPolynomialTower
