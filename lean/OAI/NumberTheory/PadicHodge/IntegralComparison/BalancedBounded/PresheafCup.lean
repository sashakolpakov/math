import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.CechAlgebraProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.BalancedBounded.CechCup

/-! # Presheaf Cup -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BalancedBounded.PresheafCup

noncomputable section

/-! The balanced original bounded crystalline cup is the literal
ambient-ring Čech cup under its native presheaf cohomology coordinates. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

private theorem transfer {C D E C' D' E' V W Z : Type*}
    (e : C ≃ C') (d : D ≃ D') (t : E → E')
    (a : C' → V) (b : D' → W) (c : E' → Z)
    (μ : C → D → E) (ν : C' → D' → E') (κ : V → W → Z)
    (hμ : ∀ x y, t (μ x y) = ν (e x) (d y))
    (hκ : ∀ x y, κ (a (e x)) (b (d y)) = c (t (μ x y)))
    (x : C') (y : D') : κ (a x) (b y) = c (ν x y) := by
  obtain ⟨x, rfl⟩ := e.surjective x
  obtain ⟨y, rfl⟩ := d.surjective y
  exact (hκ x y).trans (congrArg c (hμ x y))

private theorem normalize_product {C D E V W Z : Type*}
    (a a' : C → V) (b b' : D → W) (c c' : E → Z)
    (μ : C → D → E) (κ : V → W → Z)
    (ha : ∀ x, a x = a' x) (hb : ∀ y, b y = b' y) (hc : ∀ z, c z = c' z)
    (h : ∀ x y, κ (a' x) (b' y) = c' (μ x y)) (x : C) (y : D) :
    κ (a x) (b y) = c (μ x y) :=
  (congrArg₂ κ (ha x) (hb y)).trans ((h x y).trans (hc (μ x y)).symm)

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  {J : Ideal (WittVector p k)} {δ : DividedPowers J} {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of (WittVector p k))) [IsSeparated f] (n : ℕ)
  {ι : Type u} (F : ι → BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)
  (hcover : ∀ U, CoveringObjectsSheafDetection.sieve F U ∈ BoundedCrystalline.Site.topology f n U)

local notation "CR" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "C" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.CechComplex.presheafComplex f n F
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f n
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CechCup.cochainAlgebra f n F
local notation "N" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve F

def equivalence (i : ℕ) : (C).homology i ≃ₗ[CR] H i :=
  (Lifted.HomologyCoordinates.equivalence.{u + 1, u + 1, u + 2} CR C i).trans
    (CechCup.presheafHomologyIso p k f n F hcover i).toLinearEquiv

def cup := BoundedFrame.SheafAugmentationProduct.sourceCup f n N

theorem normalization (i : ℕ) (x : (Cosimplicial.ModuleComplex.complex A).homology i) :
    equivalence p k f n F hcover i
      (HomologicalComplex.homologyMap (Bounded.CechAlgebraProduct.comparison f n F).hom i x) =
        CechCup.cohomologyEquiv p k f n F hcover i x := by
  rw [← Bounded.CechAlgebraProduct.comparison_hom]
  rfl

theorem cup_comparison (i j : ℕ) (x : (C).homology i) (y : (C).homology j) :
    CechCup.cup p k f n F hcover i j
      (equivalence p k f n F hcover i x) (equivalence p k f n F hcover j y) =
    equivalence p k f n F hcover (i + j) (cup p k f n F i j x y) := transfer
  (HomologicalComplex.homologyMapIso (Bounded.CechAlgebraProduct.comparison f n F) i).toLinearEquiv.toEquiv
  (HomologicalComplex.homologyMapIso (Bounded.CechAlgebraProduct.comparison f n F) j).toLinearEquiv.toEquiv
  (HomologicalComplex.homologyMap (Bounded.CechAlgebraProduct.comparison f n F).hom (i + j))
  (equivalence p k f n F hcover i) (equivalence p k f n F hcover j)
  (equivalence p k f n F hcover (i + j))
  (fun x y => Cosimplicial.ModuleCup.cohomologyCup A i j x y)
  (fun x y => cup p k f n F i j x y)
  (fun x y => CechCup.cup p k f n F hcover i j x y)
  (Bounded.CechAlgebraProduct.cohomology_cup f n F i j)
  (normalize_product _ _ _ _ _ _
    (fun x y => Cosimplicial.ModuleCup.cohomologyCup A i j x y)
    (fun x y => CechCup.cup p k f n F hcover i j x y)
    (normalization p k f n F hcover i) (normalization p k f n F hcover j)
    (normalization p k f n F hcover (i + j))
    (CechCup.cup_comparison p k f n F hcover i j)) x y

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BalancedBounded.PresheafCup
