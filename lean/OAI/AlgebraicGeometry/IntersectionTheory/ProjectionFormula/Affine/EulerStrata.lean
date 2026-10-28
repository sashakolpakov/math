import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.MovedAffineWeightedEuler

/-! # Euler Strata -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.EulerStrata

noncomputable section

/-! A finite list of exceptional affine strata can be fixed before
choosing any intersecting cycle. Every cycle meeting these strata
properly has the same generic-length Euler expansion. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.FiltrationAvoidance

theorem exists_data (R : Type) [CommRing R] [IsNoetherianRing R]
    (V : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m q : ℕ) [SmoothOfRelativeDimension m V.structureMap]
    (j : Spec (.of R) ⟶ V.carrier) [IsOpenImmersion j]
    (M : ModuleCat R) [Module.Finite R M]
    (hM : ∀ v ∈ Module.support R M, q ≤ V.supportCodimension (FiltrationAvoidance.support j v)) :
    ∃ (F : Finset (PrimeSpectrum R)) (Z : Finset (IrreducibleCloseds V.carrier)),
      (∀ B ∈ Z, q < V.supportCodimension B) ∧
      (∀ z ∈ F, z ∈ Module.support R M ∧ V.supportCodimension (FiltrationAvoidance.support j z) = q ∧
        FiltrationBaseLength.length R (Localization.AtPrime z.asIdeal) M ≠ ⊤) ∧
      (∀ z : PrimeSpectrum R, V.supportCodimension (FiltrationAvoidance.support j z) = q → z ∉ F →
        FiltrationBaseLength.length R (Localization.AtPrime z.asIdeal) M = 0) ∧
      ∀ (p : ℕ) (a : V.RationalDimensionCycle p),
        a ∈ Proper.SupportCycles.submodule V p (fun B : Z => B.val) →
        ∀ A ∈ a.support, ∀ C : V.DimensionCycleSupport (p + q), ∀ x : PrimeSpectrum R,
          j x = CycleClass.Thom.IntersectionGeometry.supportPoint C.val → CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (A.val : Set V.carrier) →
          letI : Algebra R ((Spec (.of R)).presheaf.stalk x) := (StructureSheaf.toStalk R x).hom.toAlgebra
          ∀ (N : ModuleCat ((Spec (.of R)).presheaf.stalk x)) [Module.Finite ((Spec (.of R)).presheaf.stalk x) N]
            (d : ℕ) [HasProjectiveDimensionLE N d],
            Module.support ((Spec (.of R)).presheaf.stalk x)
                ((ProjectionFormula.Flat.Extension.baseChange R ((Spec (.of R)).presheaf.stalk x)).obj M) ∩
              Module.support ((Spec (.of R)).presheaf.stalk x) N ⊆
                {IsLocalRing.closedPoint ((Spec (.of R)).presheaf.stalk x)} →
            Tor.Euler.euler ((Spec (.of R)).presheaf.stalk x)
              ((ProjectionFormula.Flat.Extension.baseChange R ((Spec (.of R)).presheaf.stalk x)).obj M) N d =
            ∑ z ∈ F, ((FiltrationBaseLength.length R (Localization.AtPrime z.asIdeal) M).toNat : ℚ) *
              Tor.Euler.euler ((Spec (.of R)).presheaf.stalk x)
                ((ProjectionFormula.Flat.Extension.baseChange R ((Spec (.of R)).presheaf.stalk x)).obj
                  (.of R (R ⧸ z.asIdeal))) N d := by
  obtain ⟨k, v, hsupp, hcount, he⟩ := UniversalPrimeFiltration.exists_data R M
  have hdim (i : Fin k) : q ≤ V.supportCodimension (FiltrationAvoidance.support j (v i)) :=
    hM (v i) (hsupp i (MinimalPrimeFiltration.prime_mem_support R (v i)))
  let P := fun z : PrimeSpectrum R => V.supportCodimension (FiltrationAvoidance.support j z) = q
  let F := (Finset.univ.image v).filter P
  let Z := (Finset.univ.filter (fun i => q < V.supportCodimension (FiltrationAvoidance.support j (v i)))).image
    (fun i => FiltrationAvoidance.support j (v i))
  have hc (z : PrimeSpectrum R) (hz : P z) :
      FiltrationBaseLength.length R (Localization.AtPrime z.asIdeal) M =
        (Finset.univ.filter (fun i => v i = z)).card :=
    hcount z (PrimeCodimension.minimal V m q j M hM z hz)
  refine ⟨F, Z, ?_, ?_, ?_, ?_⟩
  · intro B hB
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hB
    exact (Finset.mem_filter.mp hi).2
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
  · intro p a ha A hA C x hx hAC
    let : Algebra R ((Spec (.of R)).presheaf.stalk x) := (StructureSheaf.toStalk R x).hom.toAlgebra
    intro N _ d _ hisolated
    let : IsLocalization x.asIdeal.primeCompl ((Spec (.of R)).presheaf.stalk x) := by
      change IsLocalization x.asIdeal.primeCompl ((structurePresheafInCommRingCat R).stalk x)
      infer_instance
    let : Module.Flat R ((Spec (.of R)).presheaf.stalk x) :=
      IsLocalization.flat _ x.asIdeal.primeCompl
    rw [he ((Spec (.of R)).presheaf.stalk x) N d
      (IsLocalRing.closedPoint ((Spec (.of R)).presheaf.stalk x)) hisolated]
    have hfilter : (∑ i ∈ Finset.univ.filter (fun i => P (v i)),
        Tor.Euler.euler ((Spec (.of R)).presheaf.stalk x)
          ((ProjectionFormula.Flat.Extension.baseChange R ((Spec (.of R)).presheaf.stalk x)).obj
            (.of R (R ⧸ (v i).asIdeal))) N d) =
        ∑ i : Fin k, Tor.Euler.euler ((Spec (.of R)).presheaf.stalk x)
          ((ProjectionFormula.Flat.Extension.baseChange R ((Spec (.of R)).presheaf.stalk x)).obj
            (.of R (R ⧸ (v i).asIdeal))) N d := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i hi hnot
      have hne : V.supportCodimension (FiltrationAvoidance.support j (v i)) ≠ q :=
        fun hh => hnot (Finset.mem_filter.mpr ⟨hi, hh⟩)
      have hbad : q < V.supportCodimension (FiltrationAvoidance.support j (v i)) := lt_of_le_of_ne (hdim i) hne.symm
      have hz : FiltrationAvoidance.support j (v i) ∈ Z :=
        Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hbad⟩, rfl⟩
      exact FiltrationAvoidance.native_euler_zero V j p q A C x (v i) hx hAC hbad (ha ⟨_, hz⟩ A hA) N d
    rw [← hfilter]
    simpa only [P, F, Finset.filter_congr_decidable] using ProjectionFormula.Finite.MultiplicitySum.reindex k v P
      (fun z => FiltrationBaseLength.length R (Localization.AtPrime z.asIdeal) M) hc
      (fun z => Tor.Euler.euler ((Spec (.of R)).presheaf.stalk x)
        ((ProjectionFormula.Flat.Extension.baseChange R ((Spec (.of R)).presheaf.stalk x)).obj
          (.of R (R ⧸ z.asIdeal))) N d)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.EulerStrata
