import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.HigherEuler
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.EulerStrata

/-! # Affine Euler -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Proper.AffineEuler

noncomputable section

/-! An actual proper pairing has the generic-length affine Euler
expansion. Higher-codimension filtration factors vanish by Serre's
theorem, so no exceptional filtration strata need to be moved against. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.FiltrationAvoidance

theorem exists_data (V : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m q : ℕ)
    [SmoothOfRelativeDimension m V.structureMap]
    (R : Type) [CommRing R] [IsNoetherianRing R]
    (j : Spec (.of R) ⟶ V.carrier) [IsOpenImmersion j]
    (M : ModuleCat R) [Module.Finite R M]
    (hM : ∀ v ∈ Module.support R M, q ≤ V.supportCodimension (Affine.FiltrationAvoidance.support j v)) :
    ∃ F : Finset (PrimeSpectrum R),
      (∀ z ∈ F, z ∈ Module.support R M ∧ V.supportCodimension (Affine.FiltrationAvoidance.support j z) = q ∧
        FiltrationBaseLength.length R (Localization.AtPrime z.asIdeal) M ≠ ⊤) ∧
      (∀ z : PrimeSpectrum R, V.supportCodimension (Affine.FiltrationAvoidance.support j z) = q → z ∉ F →
        FiltrationBaseLength.length R (Localization.AtPrime z.asIdeal) M = 0) ∧
      ∀ (p : ℕ) (Z : Finset (IrreducibleCloseds V.carrier))
        (_hZ : ∀ B ∈ Z, q ≤ V.supportCodimension B)
        (_hcover : ∀ v ∈ Module.support R M, ∃ B ∈ Z, j v ∈ (B : Set V.carrier))
        (A : V.DimensionCycleSupport p) (A₀ : IrreducibleCloseds (Spec (.of R)))
        (_hA : j (CycleClass.Thom.IntersectionGeometry.supportPoint A₀) = CycleClass.Thom.IntersectionGeometry.supportPoint A.val)
        (_hproper : ∀ B ∈ Z, ∀ D : IrreducibleCloseds V.carrier,
          (D : Set V.carrier) ⊆ (A.val : Set V.carrier) ∩ (B : Set V.carrier) →
            p + V.supportCodimension B ≤ V.supportCodimension D)
        (C : V.DimensionCycleSupport (p + q)) (x : PrimeSpectrum R)
        (_hx : j x = CycleClass.Thom.IntersectionGeometry.supportPoint C.val) (hxA : x ∈ (A₀ : Set (Spec (.of R)))),
        letI : Algebra R ((Spec (.of R)).presheaf.stalk x) := (StructureSheaf.toStalk R x).hom.toAlgebra
        Tor.Euler.euler ((Spec (.of R)).presheaf.stalk x)
          ((ProjectionFormula.Flat.Extension.baseChange R ((Spec (.of R)).presheaf.stalk x)).obj M)
          (CycleClass.Thom.IntersectionGeometry.localSupportModule (Spec (.of R)) A₀ x hxA) m =
          ∑ z ∈ F, ((FiltrationBaseLength.length R (Localization.AtPrime z.asIdeal) M).toNat : ℚ) *
            CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity V (Affine.FiltrationAvoidance.support j z) A.val C.val := by
  obtain ⟨k, v, hsupp, hcount, he⟩ := UniversalPrimeFiltration.exists_data R M
  have hdim (i : Fin k) : q ≤ V.supportCodimension (Affine.FiltrationAvoidance.support j (v i)) :=
    hM (v i) (hsupp i (MinimalPrimeFiltration.prime_mem_support R (v i)))
  let P := fun z : PrimeSpectrum R => V.supportCodimension (Affine.FiltrationAvoidance.support j z) = q
  let F := (Finset.univ.image v).filter P
  have hc (z : PrimeSpectrum R) (hz : P z) :
      FiltrationBaseLength.length R (Localization.AtPrime z.asIdeal) M =
        (Finset.univ.filter (fun i => v i = z)).card :=
    hcount z (Affine.PrimeCodimension.minimal V m q j M hM z hz)
  refine ⟨F, ?_, ?_, ?_⟩
  · intro z hz
    have hP := (Finset.mem_filter.mp hz).2
    have hs : z ∈ Module.support R M := by
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hz).1
      exact hsupp i (MinimalPrimeFiltration.prime_mem_support R (v i))
    refine ⟨hs, hP, ?_⟩
    rw [hc z hP]
    exact ENat.natCast_ne_top _
  · intro z hz hzF
    rw [hc z hz]
    have hempty : Finset.univ.filter (fun i => v i = z) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      exact hzF (Finset.mem_filter.mpr ⟨Finset.mem_image.mpr
        ⟨i, Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩, hz⟩)
    rw [hempty, Finset.card_empty, Nat.cast_zero]
  · intro p Z hZ hcover A A₀ hA hproper C x hx hxA
    let S := (Spec (.of R)).presheaf.stalk x
    let : Algebra R S := (StructureSheaf.toStalk R x).hom.toAlgebra
    let : IsLocalization x.asIdeal.primeCompl S := by
      change IsLocalization x.asIdeal.primeCompl ((structurePresheafInCommRingCat R).stalk x)
      infer_instance
    let : Module.Flat R S := IsLocalization.flat S x.asIdeal.primeCompl
    let N := CycleClass.Thom.IntersectionGeometry.localSupportModule (Spec (.of R)) A₀ x hxA
    let : Module.Finite S N := Local.TorFinite.localSupportModule_finite (Spec (.of R)) A₀ x hxA
    let : HasProjectiveDimensionLE N m :=
      Polynomial.DimensionBound.bound_of_ringEquiv (asIso (j.stalkMap x)).commRingCatIsoToRingEquiv m
        (Smooth.StalkDimension.stalk_bound V.structureMap m (j x)) N
    have hiso := Affine.CoverIsolation.isolated V m p q R j M Z hZ hcover A A₀ hA hproper C x hx hxA
    rw [he S N m (IsLocalRing.closedPoint S) hiso]
    have hfilter : (∑ i ∈ Finset.univ.filter (fun i => P (v i)),
        Tor.Euler.euler S ((ProjectionFormula.Flat.Extension.baseChange R S).obj (.of R (R ⧸ (v i).asIdeal))) N m) =
        ∑ i : Fin k, Tor.Euler.euler S
          ((ProjectionFormula.Flat.Extension.baseChange R S).obj (.of R (R ⧸ (v i).asIdeal))) N m := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i hi hnot
      have hne : V.supportCodimension (Affine.FiltrationAvoidance.support j (v i)) ≠ q :=
        fun hh => hnot (Finset.mem_filter.mpr ⟨hi, hh⟩)
      have hbad : q < V.supportCodimension (Affine.FiltrationAvoidance.support j (v i)) := lt_of_le_of_ne (hdim i) hne.symm
      apply Affine.HigherEuler.zero V m p q R j (v i) hbad A A₀ hA C x hx hxA
      exact Affine.CoverIsolation.isolated V m p q R j (.of R (R ⧸ (v i).asIdeal)) Z hZ
        (fun z hz => hcover z (hsupp i hz)) A A₀ hA hproper C x hx hxA
    rw [← hfilter]
    calc
      _ = ∑ z ∈ F, ((FiltrationBaseLength.length R (Localization.AtPrime z.asIdeal) M).toNat : ℚ) *
          Tor.Euler.euler S ((ProjectionFormula.Flat.Extension.baseChange R S).obj (.of R (R ⧸ z.asIdeal))) N m := by
        simpa only [P, F, Finset.filter_congr_decidable] using ProjectionFormula.Finite.MultiplicitySum.reindex k v P
          (fun z => FiltrationBaseLength.length R (Localization.AtPrime z.asIdeal) M) hc
          (fun z => Tor.Euler.euler S ((ProjectionFormula.Flat.Extension.baseChange R S).obj (.of R (R ⧸ z.asIdeal))) N m)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro z _
        rw [Affine.Prime.euler V m R j z A₀ A.val C.val hA x hx hxA]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Proper.AffineEuler
