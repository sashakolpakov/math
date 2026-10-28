import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechCupNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CrystallineInverseLimit
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.InverseLimitCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.InverseTransitionCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.CompatibleBilinearProduct

/-! # Crystalline Cup -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.CrystallineCup

noncomputable section

/-! A cup product on the original integral crystalline Ext cohomology.
Its finite-level coordinates are the native Witt-frame products. Projectivity
is used only by the existing finite-level finiteness theorem that proves the
inverse-limit equivalence in every degree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k X
local notation "DP" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "PIdeal" => Ideal.span {(p : WittVector p k)}

abbrev Compatible (i : ℕ) :=
  Crystalline.CohomologyDifference.compatible (p := p) (J := PIdeal) (δ := DP) f i

omit [Fintype k] [IsProper X.hom] [Smooth X.hom] in
theorem compatible_transition (i : ℕ) (x : Compatible p k X i) (n : ℕ) :
    Bounded.CohomologyTransition.map f n (n + 1) (Nat.le_succ n) i (x.val (n + 1)) = x.val n := by
  have h := (Crystalline.CohomologyDifference.mem_compatible f i x.val).mp x.property n
  rw [Crystalline.InverseTransitionCoordinates.transition] at h
  exact h

theorem product_compatible (i j : ℕ) (x : Compatible p k X i) (y : Compatible p k X j) :
    (fun n => SmoothProper.WittCechCup.cup p k X n i j (x.val n) (y.val n)) ∈
      Crystalline.CohomologyDifference.compatible (p := p) (J := PIdeal) (δ := DP) f (i + j) := by
  apply (Crystalline.CohomologyDifference.mem_compatible f (i + j) _).mpr
  intro n
  rw [Crystalline.InverseTransitionCoordinates.transition]
  exact (SmoothProper.WittCechCupNaturality.cup_natural p k X n (n + 1) (Nat.le_succ n)
    i j (x.val (n + 1)) (y.val (n + 1))).trans
      (congrArg₂ (fun a b => SmoothProper.WittCechCup.cup p k X n i j a b)
        (compatible_transition p k X i x n) (compatible_transition p k X j y n))

def compatibleProduct (i j : ℕ) (x : Compatible p k X i) (y : Compatible p k X j) :
    Compatible p k X (i + j) :=
  ⟨fun n => SmoothProper.WittCechCup.cup p k X n i j (x.val n) (y.val n),
    product_compatible p k X i j x y⟩

def compatibleCup (i j : ℕ) : Compatible p k X i →ₗ[R]
    Compatible p k X j →ₗ[R] Compatible p k X (i + j) :=
  CompatibleBilinearProduct.cup R
    (fun n i => BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := PIdeal) (δ := DP) f n i)
    (fun i => Crystalline.CohomologyDifference.compatible (p := p) (J := PIdeal) (δ := DP) f i)
    (SmoothProper.WittCechCup.cup p k X) (product_compatible p k X) i j

theorem compatibleCup_coordinate (i j n : ℕ) (x : Compatible p k X i) (y : Compatible p k X j) :
    (compatibleCup p k X i j x y).val n = SmoothProper.WittCechCup.cup p k X n i j (x.val n) (y.val n) :=
  CompatibleBilinearProduct.coordinate R
    (fun n i => BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := PIdeal) (δ := DP) f n i)
    (fun i => Crystalline.CohomologyDifference.compatible (p := p) (J := PIdeal) (δ := DP) f i)
    (SmoothProper.WittCechCup.cup p k X) (product_compatible p k X) i j n x y

variable (hprojective : Projectivity.Construction.ProjectiveOver k X.hom)

abbrev equivalence (i : ℕ) : Witt.Crystalline.integralCohomology p k X i ≃ₗ[R] Compatible p k X i :=
  SmoothProper.CrystallineInverseLimit.compatibleEquiv p k X hprojective i

/-- Integral cup on the original small-site crystalline Ext groups. -/
def cup (i j : ℕ) : Witt.Crystalline.integralCohomology p k X i →ₗ[R]
    Witt.Crystalline.integralCohomology p k X j →ₗ[R] Witt.Crystalline.integralCohomology p k X (i + j) :=
  (((compatibleCup p k X i j).comp (equivalence p k X hprojective i).toLinearMap).compl₂
    (equivalence p k X hprojective j).toLinearMap).compr₂
      (equivalence p k X hprojective (i + j)).symm.toLinearMap

theorem cup_coordinates (i j : ℕ) (x : Witt.Crystalline.integralCohomology p k X i) (y : Witt.Crystalline.integralCohomology p k X j) :
    equivalence p k X hprojective (i + j) (cup p k X hprojective i j x y) =
      compatibleCup p k X i j (equivalence p k X hprojective i x) (equivalence p k X hprojective j y) := by
  simp only [cup, LinearMap.compr₂_apply, LinearMap.compl₂_apply,
    LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]

def restriction (n i : ℕ) : Witt.Crystalline.integralCohomology p k X i →ₗ[R]
    BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := PIdeal) (δ := DP) f n i :=
  (BoundedCrystalline.CrystallineCohomology.restriction f n i).comp
    (Global.Crystalline.Comparison.integralEquiv p k X i).symm.toLinearMap

theorem equivalence_coordinate (i n : ℕ) (x : Witt.Crystalline.integralCohomology p k X i) :
    (equivalence p k X hprojective i x).val n = restriction p k X n i x := by
  let := SmoothProper.CrystallineInverseLimit.inclusion_mono p k X hprojective i
  exact Crystalline.InverseLimitCoordinates.compatible_coordinate f i
    ((Global.Crystalline.Comparison.integralEquiv p k X i).symm x) n

/-- Restriction to each original bounded crystalline site preserves the product. -/
theorem restriction_cup (n i j : ℕ) (x : Witt.Crystalline.integralCohomology p k X i) (y : Witt.Crystalline.integralCohomology p k X j) :
    restriction p k X n (i + j) (cup p k X hprojective i j x y) =
      SmoothProper.WittCechCup.cup p k X n i j (restriction p k X n i x) (restriction p k X n j y) := by
  exact (equivalence_coordinate p k X hprojective (i + j) n (cup p k X hprojective i j x y)).symm.trans
    ((congrArg (fun z : Compatible p k X (i + j) => z.val n) (cup_coordinates p k X hprojective i j x y)).trans
      ((compatibleCup_coordinate p k X i j n
        (equivalence p k X hprojective i x) (equivalence p k X hprojective j y)).trans
          (congrArg₂ (fun a b => SmoothProper.WittCechCup.cup p k X n i j a b)
            (equivalence_coordinate p k X hprojective i n x) (equivalence_coordinate p k X hprojective j n y))))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.CrystallineCup
