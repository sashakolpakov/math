import OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline
import OAI.NumberTheory.PadicHodge.IntegralComparison.Zero.ObjectExt

/-! # Empty Crystalline Cohomology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.EmptyCrystallineCohomology

noncomputable section

/-! All original integral and rational crystalline cohomology groups of an empty scheme vanish. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Site

section General

variable (p : ℕ) (B : Type u) [CommRing B] (J : Ideal B) (δ : DividedPowers J)
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) [IsEmpty X]

theorem ring (U : Crystalline.Site.AffineThickening p B J δ f) : Subsingleton U.ring := by
  let : IsEmpty (PrimeSpectrum (U.ring ⧸ U.ideal)) := ⟨fun x => isEmptyElim (U.openMap x)⟩
  let : Subsingleton (U.ring ⧸ U.ideal) := PrimeSpectrum.isEmpty_iff_subsingleton.mp inferInstance
  have h : (1 : U.ring) ∈ U.ideal := Ideal.Quotient.eq_zero_iff_mem.mp (Subsingleton.elim _ _)
  obtain ⟨n, hn⟩ := U.nilIdeal 1 h
  exact subsingleton_of_zero_eq_one (by simpa only [one_pow] using hn.symm)

theorem presheaf : IsZero (Crystalline.Site.AffineThickening.structureModulePresheafLarge (p := p) (B := B) (J := J) (δB := δ) (f := f)) := by
  rw [Functor.isZero_iff]
  intro U
  let := EmptyCrystallineCohomology.ring p B J δ f U.unop
  let : Subsingleton ((Crystalline.Site.AffineThickening.structureModulePresheafLarge (p := p) (B := B) (J := J) (δB := δ) (f := f)).obj U) := by
    constructor
    intro x y
    apply ULift.ext
    exact @Subsingleton.elim U.unop.ring inferInstance x.down y.down
  exact ModuleCat.isZero_of_subsingleton _

theorem sheaf : IsZero (Crystalline.Site.AffineThickening.structureModuleSheaf (p := p) (B := B) (J := J) (δB := δ) (f := f)) :=
  (presheafToSheaf _ _).map_isZero (presheaf p B J δ f)

theorem integral (n : ℕ) :
    Subsingleton (Crystalline.Site.AffineThickening.IntegralModuleCohomology (p := p) (B := B) (J := J) (δB := δ) (f := f) n) :=
  Zero.ObjectExt.target _ _ n (sheaf p B J δ f)

end General

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsEmpty X.left]

theorem rational (n : ℕ) : Subsingleton (Witt.Crystalline.rationalCohomology p k X n) := by
  let := integral p (WittVector p k) (Ideal.span {(p : WittVector p k)})
    (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) n
  exact inferInstanceAs (Subsingleton (TensorProduct (WittVector p k) (FractionRing (WittVector p k))
    (Witt.Crystalline.integralCohomology p k X n)))

theorem finite (n : ℕ) :
    FiniteDimensional (FractionRing (WittVector p k)) (Witt.Crystalline.rationalCohomology p k X n) := by
  let := rational p k X n
  infer_instance

theorem charpoly (n : ℕ)
    (f : Module.End (FractionRing (WittVector p k)) (Witt.Crystalline.rationalCohomology p k X n)) :
    letI := finite p k X n
    f.charpoly = 1 := by
  let := rational p k X n
  have hf : f = 0 := Subsingleton.elim _ _
  rw [hf, LinearMap.charpoly_zero, Module.finrank_zero_of_subsingleton, pow_zero]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.EmptyCrystallineCohomology
