import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.PrimeCodimension

/-! # Moved Affine Filtration Euler -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.MovedAffineFiltrationEuler

noncomputable section

/-! After moving against the finitely many higher-codimension strata
of one fixed affine filtration, every relevant local Euler pairing is
computed solely by its factors in the expected codimension. Their
multiplicities are the native generic module lengths. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.FiltrationAvoidance

theorem exists_moved (R : Type) [CommRing R] [IsNoetherianRing R]
    (V : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p q : ℕ) [SmoothOfRelativeDimension m V.structureMap]
    (j : Spec (.of R) ⟶ V.carrier) [IsOpenImmersion j]
    (M : ModuleCat R) [Module.Finite R M]
    (hM : ∀ v ∈ Module.support R M, q ≤ V.supportCodimension (Affine.FiltrationAvoidance.support j v))
    (a : V.RationalDimensionCycle p) :
    ∃ (k : ℕ) (v : Fin k → PrimeSpectrum R) (a' : V.RationalDimensionCycle p),
      CycleClass.Thom.IntersectionGeometry.RationallyEquivalent V p a a' ∧
      (∀ i, q ≤ V.supportCodimension (Affine.FiltrationAvoidance.support j (v i))) ∧
      (∀ z : PrimeSpectrum R, V.supportCodimension (Affine.FiltrationAvoidance.support j z) = q →
        FiltrationBaseLength.length R (Localization.AtPrime z.asIdeal) M =
          (Finset.univ.filter (fun i => v i = z)).card) ∧
      ∀ A ∈ a'.support, ∀ C : V.DimensionCycleSupport (p + q), ∀ x : PrimeSpectrum R,
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
          ∑ i ∈ Finset.univ.filter (fun i => V.supportCodimension (Affine.FiltrationAvoidance.support j (v i)) = q),
            Tor.Euler.euler ((Spec (.of R)).presheaf.stalk x)
              ((ProjectionFormula.Flat.Extension.baseChange R ((Spec (.of R)).presheaf.stalk x)).obj
                (.of R (R ⧸ (v i).asIdeal))) N d := by
  obtain ⟨k, v, hsupp, hcount, he⟩ := UniversalPrimeFiltration.exists_data R M
  have hdim (i : Fin k) : q ≤ V.supportCodimension (Affine.FiltrationAvoidance.support j (v i)) :=
    hM (v i) (hsupp i (MinimalPrimeFiltration.prime_mem_support R (v i)))
  let I := {i : Fin k // q < V.supportCodimension (Affine.FiltrationAvoidance.support j (v i))}
  obtain ⟨a', ha', hproper⟩ := General.ChowMoving.cycle V m (fun i : I => Affine.FiltrationAvoidance.support j (v i.val)) p a
  refine ⟨k, v, a', ha', hdim, ?_, ?_⟩
  · intro z hz
    exact hcount z (Affine.PrimeCodimension.minimal V m q j M hM z hz)
  · intro A hA C x hx hAC
    let : Algebra R ((Spec (.of R)).presheaf.stalk x) := (StructureSheaf.toStalk R x).hom.toAlgebra
    intro N _ d _ hisolated
    let : IsLocalization x.asIdeal.primeCompl ((Spec (.of R)).presheaf.stalk x) := by
      change IsLocalization x.asIdeal.primeCompl ((structurePresheafInCommRingCat R).stalk x)
      infer_instance
    let : Module.Flat R ((Spec (.of R)).presheaf.stalk x) :=
      IsLocalization.flat _ x.asIdeal.primeCompl
    rw [he ((Spec (.of R)).presheaf.stalk x) N d
      (IsLocalRing.closedPoint ((Spec (.of R)).presheaf.stalk x)) hisolated]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hi hnot
    have hne : V.supportCodimension (Affine.FiltrationAvoidance.support j (v i)) ≠ q :=
      fun hh => hnot (Finset.mem_filter.mpr ⟨hi, hh⟩)
    have hbad : q < V.supportCodimension (Affine.FiltrationAvoidance.support j (v i)) := lt_of_le_of_ne (hdim i) hne.symm
    exact Affine.FiltrationAvoidance.native_euler_zero V j p q A C x (v i) hx hAC hbad (hproper ⟨i, hbad⟩ A hA) N d

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.MovedAffineFiltrationEuler
