import OAI.AlgebraicGeometry.FormalGeometry.Completion.Frobenius
import OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineFrobenius
import OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter

/-! # Frobenius Adapter -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.FrobeniusAdapter.CrystallineAdapter

noncomputable section

/-! Agreement of the two independently constructed Frobenius morphisms at a split prime. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

theorem bigPullback_congr {p : ℕ} {B : Type} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
    {X Y : Scheme} {fX : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
    {g h : X ⟶ Y} (e : g = h) (hg : g ≫ fY = fX) (hh : h ≫ fY = fX) (n : ℕ) :
    IntegralComparison.BigCrystallineCohomology.pullback (p := p) (J := J) (δ := δ) g hg n =
      IntegralComparison.BigCrystallineCohomology.pullback (p := p) (J := J) (δ := δ) h hh n := by
  subst h
  rfl

variable (q : ℕ) [Fact q.Prime] (X : Over (Spec (CommRingCat.of (ZMod q))))

theorem schemeFrobenius_eq :
    IntegralComparison.BigCrystallineFrobenius.schemeFrobenius q (ZMod q) X 1 =
      (AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius (ZMod q) X).left := by
  change (𝟙 X.left ≫ AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q (Fact.out : q.Prime) X.left
    (IntegralComparison.Global.FrobeniusGeometry.scheme_prime_zero q (ZMod q) X.hom)) = _
  rw [Category.id_comp]
  apply Scheme.Hom.ext (by rfl)
  intro U
  change (AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q (Fact.out : q.Prime) X.left
      (IntegralComparison.Global.FrobeniusGeometry.scheme_prime_zero q (ZMod q) X.hom)).app U ≫
    X.left.presheaf.map (𝟙 (op U)) =
      (AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.qPowerSchemeFrobenius (ZMod q) X.left (AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.varietyBaseMap (ZMod q) X)).app U
  erw [X.left.presheaf.map_id, Category.comp_id]
  ext a
  change a ^ q = a ^ Fintype.card (ZMod q)
  rw [ZMod.card]

theorem integralFrobenius_eq (n : ℕ)
    (x : IntegralComparison.BigCrystallineFrobenius.IntegralCohomology q (ZMod q) X n) :
    IntegralComparison.BigCrystallineFrobenius.integralFrobenius q (ZMod q) X 1
        (by rw [ZMod.card, pow_one]) n x =
      Crystalline.CoefficientAdapter.integralPullback (p := q) (J := Ideal.span {(q : Crystalline.CoefficientAdapter.Witt q)})
        (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers q (ZMod q))
        (f := Crystalline.CoefficientAdapter.wittStructure q X) (fY := Crystalline.CoefficientAdapter.wittStructure q X)
        (AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius (ZMod q) X).left
        (show (AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius (ZMod q) X).left ≫
            Crystalline.CoefficientAdapter.wittStructure q X = Crystalline.CoefficientAdapter.wittStructure q X from by
          simp only [Crystalline.CoefficientAdapter.wittStructure, ← Category.assoc, Over.w]) n x := by
  let g := IntegralComparison.BigCrystallineFrobenius.schemeFrobenius q (ZMod q) X 1
  let h := (AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius (ZMod q) X).left
  have hg : g ≫ Crystalline.CoefficientAdapter.wittStructure q X = Crystalline.CoefficientAdapter.wittStructure q X :=
    IntegralComparison.BigCrystallineFrobenius.schemeFrobenius_over_witt q (ZMod q) X 1
      (by rw [ZMod.card, pow_one])
  have hh : h ≫ Crystalline.CoefficientAdapter.wittStructure q X = Crystalline.CoefficientAdapter.wittStructure q X := by
    simp only [h, Crystalline.CoefficientAdapter.wittStructure, ← Category.assoc, Over.w]
  change IntegralComparison.BigCrystallineCohomology.pullback (p := q)
    (J := Ideal.span {(q : Crystalline.CoefficientAdapter.Witt q)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers q (ZMod q))
      g hg n x = IntegralComparison.BigCrystallineCohomology.pullback (p := q)
    (J := Ideal.span {(q : Crystalline.CoefficientAdapter.Witt q)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers q (ZMod q)) h hh n x
  have hp := bigPullback_congr (p := q)
    (J := Ideal.span {(q : Crystalline.CoefficientAdapter.Witt q)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers q (ZMod q))
    (fX := Crystalline.CoefficientAdapter.wittStructure q X) (fY := Crystalline.CoefficientAdapter.wittStructure q X)
    (schemeFrobenius_eq q X) hg hh n
  exact DFunLike.congr_fun hp x

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.FrobeniusAdapter.CrystallineAdapter
