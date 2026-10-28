import OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology
import OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.Topology
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers
import Mathlib.RingTheory.WittVector.Compare

/-! # Coefficient Adapter -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter

noncomputable section

section

/-! Rationalization of IntegralComparison's genuine big crystalline cohomology over the
split base. Pullback is its proved exact-sheaf Ext construction. The scalar
map is the canonical W(𝔽_q) → ℤ_q → ℚ_q, independent of comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable {p : ℕ} {B : Type} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y : Scheme} {f : X ⟶ Spec (CommRingCat.of B)}
  {fY : Y ⟶ Spec (CommRingCat.of B)}

abbrev IntegralCohomology (p : ℕ) (B : Type) [CommRing B] (J : Ideal B)
    (δ : DividedPowers J) {X : Scheme} (f : X ⟶ Spec (CommRingCat.of B)) (n : ℕ) :=
  IntegralComparison.BigCrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f n

/-- The actual integral crystalline pullback, with its base-ring scalars. -/
def integralPullback (g : X ⟶ Y) (hg : g ≫ fY = f) (n : ℕ) :
    IntegralCohomology p B J δ fY n →ₗ[B] IntegralCohomology p B J δ f n := by
  let T : IntegralCohomology p B J δ fY n →ₗ[ULift.{1} B]
      IntegralCohomology p B J δ f n :=
    IntegralComparison.BigCrystallineCohomology.pullback g hg n
  exact
    { toFun := T
      map_add' := T.map_add
      map_smul' b x := by
        change T ((ULift.up b : ULift.{1} B) • x) = (ULift.up b : ULift.{1} B) • T x
        exact T.map_smul _ _ }

variable (q : ℕ) [Fact q.Prime]

abbrev Witt := WittVector q (ZMod q)

def wittToPadicField : Witt q →+* ℚ_[q] :=
  (algebraMap ℤ_[q] ℚ_[q]).comp (WittVector.equiv q).toRingHom

/-- The coefficient-field identification at the completely split prime. -/
def coefficientFieldEquiv : FractionRing (Witt q) ≃+* ℚ_[q] :=
  IsFractionRing.ringEquivOfRingEquiv (WittVector.equiv q)

theorem coefficientFieldEquiv_algebraMap (x : Witt q) :
    coefficientFieldEquiv q (algebraMap (Witt q) (FractionRing (Witt q)) x) =
      wittToPadicField q x :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap (WittVector.equiv q) x

instance wittPadicAlgebra : Algebra (Witt q) ℚ_[q] := (wittToPadicField q).toAlgebra

def wittStructure (X : Over (Spec (CommRingCat.of (ZMod q)))) :
    X.left ⟶ Spec (CommRingCat.of (Witt q)) :=
  X.hom ≫ Spec.map (CommRingCat.ofHom (WittVector.constantCoeff : Witt q →+* ZMod q))

abbrev IntegralH1 (X : Over (Spec (CommRingCat.of (ZMod q)))) :=
  IntegralCohomology q (Witt q) (Ideal.span {(q : Witt q)})
    (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers q (ZMod q)) (wittStructure q X) 1

abbrev RationalH1 (X : Over (Spec (CommRingCat.of (ZMod q)))) :=
  ℚ_[q] ⊗[Witt q] IntegralH1 q X

def rationalPullback {X Y : Over (Spec (CommRingCat.of (ZMod q)))} (f : X ⟶ Y) :
    RationalH1 q Y →ₗ[ℚ_[q]] RationalH1 q X :=
  (integralPullback (p := q) (J := Ideal.span {(q : Witt q)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers q (ZMod q))
    f.left (by simp only [wittStructure, ← Category.assoc, Over.w]) 1).baseChange ℚ_[q]

end

/-! Explicit change from the Witt fraction field to the split p-adic coefficient field. -/

open scoped TensorProduct

variable (q : ℕ) [Fact q.Prime]

def coefficientAlgEquiv : FractionRing (Witt q) ≃ₐ[Witt q] ℚ_[q] where
  __ := coefficientFieldEquiv q
  commutes' := coefficientFieldEquiv_algebraMap q

instance coefficientInvPair : RingHomInvPair (coefficientFieldEquiv q).toRingHom
    (coefficientFieldEquiv q).symm.toRingHom := RingHomInvPair.of_ringEquiv (coefficientFieldEquiv q)

instance coefficientInvPair_symm : RingHomInvPair (coefficientFieldEquiv q).symm.toRingHom
    (coefficientFieldEquiv q).toRingHom := RingHomInvPair.of_ringEquiv_symm (coefficientFieldEquiv q)

variable (M : Type*) [AddCommGroup M] [Module (Witt q) M]

def coefficientTensorWittEquiv :
    FractionRing (Witt q) ⊗[Witt q] M ≃ₗ[Witt q] ℚ_[q] ⊗[Witt q] M :=
  TensorProduct.congr (coefficientAlgEquiv q).toLinearEquiv (LinearEquiv.refl (Witt q) M)

/-- The actual coefficient change is semilinear for the canonical fraction-field isomorphism. -/
def coefficientTensorEquiv : FractionRing (Witt q) ⊗[Witt q] M ≃ₛₗ[(coefficientFieldEquiv q).toRingHom]
    ℚ_[q] ⊗[Witt q] M where
  __ := (coefficientTensorWittEquiv q M).toAddEquiv
  map_smul' a x := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy =>
      change coefficientTensorWittEquiv q M (a • (x + y)) =
        coefficientFieldEquiv q a • coefficientTensorWittEquiv q M (x + y)
      rw [smul_add, (coefficientTensorWittEquiv q M).map_add,
        (coefficientTensorWittEquiv q M).map_add, smul_add]
      exact congrArg₂ (· + ·) hx hy
    | tmul b m =>
      change coefficientFieldEquiv q (a * b) ⊗ₜ[Witt q] m =
        (coefficientFieldEquiv q a * coefficientFieldEquiv q b) ⊗ₜ[Witt q] m
      rw [map_mul]

theorem coefficientTensorEquiv_tmul (a : FractionRing (Witt q)) (m : M) :
    coefficientTensorEquiv q M (a ⊗ₜ[Witt q] m) = coefficientFieldEquiv q a ⊗ₜ[Witt q] m := rfl

theorem coefficientTensorEquiv_map {N : Type*} [AddCommGroup N] [Module (Witt q) N]
    (T : M →ₗ[Witt q] N) (x : FractionRing (Witt q) ⊗[Witt q] M) :
    coefficientTensorEquiv q N (T.baseChange (FractionRing (Witt q)) x) =
      T.baseChange ℚ_[q] (coefficientTensorEquiv q M x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a m => rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter
