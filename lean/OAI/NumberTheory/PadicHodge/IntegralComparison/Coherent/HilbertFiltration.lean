import OAI.NumberTheory.PadicHodge.IntegralComparison.Coherent.KTheory
import OAI.AlgebraicGeometry.FormalGeometry.Completion.IntegralProjectiveNumerics
import OAI.AlgebraicGeometry.FormalGeometry.Completion.RegularTensorSection
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialLeadingDegreeDrop
import OAI.AlgebraicGeometry.SheafCohomology.Projective.FiniteGlobalGenerators

/-! # Hilbert Filtration -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Coherent.HilbertFiltration.ProjectiveK

noncomputable section

/-! The actual coherent Grothendieck group of a closed projective scheme
has a Hilbert-degree filtration. Tensoring by a line bundle preserves it;
the difference from identity lowers it for a generated line bundle. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry MonoidalCategory

universe u
attribute [local instance] MvPolynomial.gradedAlgebra AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory

variable {K : Type u} [Field K] {r : ℕ} {A : Scheme.{u}}
  (f : A ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K))
  [IsClosedImmersion f] (j : Fin (r + 1))

def coherentHilbertPolynomial (M : KTheory.Projective.CoherentModule A) : Polynomial ℚ :=
  AlgebraicGeometry.FormalGeometry.Completion.ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial f M.sheaf j

theorem coherentHilbertPolynomial_eq_zero_iff (M : KTheory.Projective.CoherentModule A) :
    coherentHilbertPolynomial f j M = 0 ↔ IsZero M.sheaf := by
  constructor
  · intro h
    by_contra hn
    have hp := AlgebraicGeometry.FormalGeometry.Completion.ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial_leadingCoeff_pos f M.sheaf j hn
    change 0 < (coherentHilbertPolynomial f j M).leadingCoeff at hp
    rw [h, Polynomial.leadingCoeff_zero] at hp
    exact (lt_irrefl 0) hp
  · intro h
    exact AlgebraicGeometry.FormalGeometry.Completion.HilbertPositivity.Construction.projectiveHilbertPolynomial_eq_zero_of_isZero (AlgebraicGeometry.FormalGeometry.Completion.ClosedHilbertNumerics.Construction.coherentClosedDirectImage f M.sheaf) j
      ((Scheme.Modules.pushforward f).map_isZero h)

def coherentHilbertFiltration (d : ℕ) : AddSubgroup (KTheory.Projective.CoherentK0 A) :=
  AddSubgroup.closure {x | ∃ M : KTheory.Projective.CoherentModule A,
    (coherentHilbertPolynomial f j M).degree < (d : WithBot ℕ) ∧ x = KTheory.Projective.coherentK0Class M}

theorem coherentK0Class_mem_hilbertFiltration (M : KTheory.Projective.CoherentModule A) (d : ℕ)
    (hM : (coherentHilbertPolynomial f j M).degree < (d : WithBot ℕ)) :
    KTheory.Projective.coherentK0Class M ∈ coherentHilbertFiltration f j d :=
  AddSubgroup.subset_closure ⟨M, hM, rfl⟩

theorem coherentHilbertFiltration_mono {d e : ℕ} (h : d ≤ e) :
    coherentHilbertFiltration f j d ≤ coherentHilbertFiltration f j e := by
  apply AddSubgroup.closure_mono
  rintro x ⟨M, hM, rfl⟩
  exact ⟨M, hM.trans_le (WithBot.coe_le_coe.mpr h), rfl⟩

theorem coherentHilbertFiltration_zero : coherentHilbertFiltration f j 0 = ⊥ := by
  apply le_antisymm _ bot_le
  apply (AddSubgroup.closure_le _).mpr
  rintro x ⟨M, hM, rfl⟩
  have hz : coherentHilbertPolynomial f j M = 0 :=
    Polynomial.degree_eq_bot.mp (Nat.WithBot.lt_zero_iff.mp hM)
  exact KTheory.Projective.coherentK0Class_eq_zero_of_isZero M ((coherentHilbertPolynomial_eq_zero_iff f j M).mp hz)

theorem coherentHilbertPolynomial_cokernel {M N : KTheory.Projective.CoherentModule A}
    (a : M.sheaf ⟶ N.sheaf) [Mono a] :
    coherentHilbertPolynomial f j (KTheory.Projective.coherentCokernel a) =
      coherentHilbertPolynomial f j N - coherentHilbertPolynomial f j M :=
  AlgebraicGeometry.FormalGeometry.Completion.ClosedHilbertAdditivity.Construction.closedProjectiveCokernelHilbertPolynomial_eq_sub f a j

variable [IsIntegral A] [Infinite K]

theorem coherentHilbertPolynomial_tensor_leading (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A) (M : KTheory.Projective.CoherentModule A) :
    (coherentHilbertPolynomial f j
      (KTheory.Projective.coherentTensorModule L.sheaf (AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.invertible L) M)).natDegree =
        (coherentHilbertPolynomial f j M).natDegree ∧
    (coherentHilbertPolynomial f j
      (KTheory.Projective.coherentTensorModule L.sheaf (AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.invertible L) M)).leadingCoeff =
        (coherentHilbertPolynomial f j M).leadingCoeff :=
  AlgebraicGeometry.FormalGeometry.Completion.IntegralProjectiveNumerics.Construction.integralClosedProjective_coherentLineBundle_hilbert_degree_leadingCoeff f M.sheaf L j

theorem coherentHilbertPolynomial_tensor_degree (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A) (M : KTheory.Projective.CoherentModule A) :
    (coherentHilbertPolynomial f j
      (KTheory.Projective.coherentTensorModule L.sheaf (AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.invertible L) M)).degree =
        (coherentHilbertPolynomial f j M).degree := by
  let P := coherentHilbertPolynomial f j M
  let Q := coherentHilbertPolynomial f j
    (KTheory.Projective.coherentTensorModule L.sheaf (AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.invertible L) M)
  obtain ⟨hdeg, hlc⟩ := coherentHilbertPolynomial_tensor_leading f j L M
  change Q.natDegree = P.natDegree at hdeg
  change Q.leadingCoeff = P.leadingCoeff at hlc
  change Q.degree = P.degree
  by_cases hp : P = 0
  · have hq : Q = 0 := Polynomial.leadingCoeff_eq_zero.mp
      (by simpa only [hp, Polynomial.leadingCoeff_zero] using hlc)
    rw [hp, hq]
  · have hq : Q ≠ 0 := Polynomial.leadingCoeff_ne_zero.mp
      (hlc ▸ Polynomial.leadingCoeff_ne_zero.mpr hp)
    rw [Polynomial.degree_eq_natDegree hq, Polynomial.degree_eq_natDegree hp, hdeg]

theorem coherentTensorK0_mem_hilbertFiltration (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A) (d : ℕ)
    (x : KTheory.Projective.CoherentK0 A) (hx : x ∈ coherentHilbertFiltration f j d) :
    KTheory.Projective.coherentTensorK0 L.sheaf (AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.invertible L) x ∈
      coherentHilbertFiltration f j d := by
  have hh : coherentHilbertFiltration f j d ≤
      (coherentHilbertFiltration f j d).comap
        (KTheory.Projective.coherentTensorK0 L.sheaf (AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.invertible L)) := by
    apply (AddSubgroup.closure_le _).mpr
    rintro y ⟨M, hM, rfl⟩
    change KTheory.Projective.coherentTensorK0 L.sheaf (AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.invertible L)
      (KTheory.Projective.coherentK0Class M) ∈ coherentHilbertFiltration f j d
    rw [KTheory.Projective.coherentTensorK0_class]
    apply coherentK0Class_mem_hilbertFiltration
    rw [coherentHilbertPolynomial_tensor_degree]
    exact hM
  exact hh hx

theorem coherentTensorCokernel_hilbertDegree (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A) (M : KTheory.Projective.CoherentModule A)
    (a : M.sheaf ⟶ (KTheory.Projective.coherentTensorModule L.sheaf (AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.invertible L) M).sheaf)
    [Mono a] (d : ℕ)
    (hM : (coherentHilbertPolynomial f j M).degree < ((d + 1 : ℕ) : WithBot ℕ)) :
    (coherentHilbertPolynomial f j (KTheory.Projective.coherentCokernel a)).degree < (d : WithBot ℕ) := by
  rw [coherentHilbertPolynomial_cokernel]
  obtain ⟨hdeg, hlc⟩ := coherentHilbertPolynomial_tensor_leading f j L M
  exact AlgebraicGeometry.SheafCohomology.Projective.PolynomialLeadingDegreeDrop.polynomial_sub_degree_lt_of_same_leading_data _ _ hdeg hlc d hM

include f in
theorem exists_generated_tensor_mono (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A)
    (hG : AlgebraicGeometry.SheafCohomology.Projective.FiniteGlobalGenerators.HasFiniteGlobalGenerators L.sheaf) (M : KTheory.Projective.CoherentModule A) :
    ∃ a : M.sheaf ⟶ (KTheory.Projective.coherentTensorModule L.sheaf (AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.invertible L) M).sheaf,
      Mono a := by
  have : IsLocallyNoetherian A := AlgebraicGeometry.FormalGeometry.Completion.IntegralProjectiveNumerics.Construction.closedProjective_locallyNoetherian f
  have : CompactSpace A := AlgebraicGeometry.FormalGeometry.Completion.IntegralProjectiveNumerics.Construction.closedProjective_compact f
  have : Infinite Γ(A, ⊤) := AlgebraicGeometry.FormalGeometry.Completion.IntegralProjectiveNumerics.Construction.integralClosedProjective_globalFunctions_infinite f
  have hframes : AlgebraicGeometry.FormalGeometry.Completion.Frame.SectionDetection.Construction.HasFrameSections L.sheaf := by
    obtain ⟨I, hI, s, hs⟩ := hG.section_cover L
    intro x
    obtain ⟨i, hi⟩ := hs x
    exact ⟨s i, hi⟩
  exact AlgebraicGeometry.FormalGeometry.Completion.RegularTensorSection.Construction.exists_mono_tensor_generated_lineBundle (AlgebraicGeometry.FormalGeometry.Completion.IntegralProjectiveNumerics.Construction.integralClosedProjective_globalFunctions_isField f)
    L hframes M.sheaf

theorem generated_tensorDifference_class_mem_hilbertFiltration (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A)
    (hG : AlgebraicGeometry.SheafCohomology.Projective.FiniteGlobalGenerators.HasFiniteGlobalGenerators L.sheaf) (M : KTheory.Projective.CoherentModule A) (d : ℕ)
    (hM : (coherentHilbertPolynomial f j M).degree < ((d + 1 : ℕ) : WithBot ℕ)) :
    KTheory.Projective.coherentTensorK0 L.sheaf (AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.invertible L) (KTheory.Projective.coherentK0Class M) -
      KTheory.Projective.coherentK0Class M ∈ coherentHilbertFiltration f j d := by
  obtain ⟨a, ha⟩ := exists_generated_tensor_mono f L hG M
  have := ha
  rw [KTheory.Projective.coherentTensorK0_class, ← KTheory.Projective.coherentCokernel_class a]
  exact coherentK0Class_mem_hilbertFiltration f j (KTheory.Projective.coherentCokernel a) d
    (coherentTensorCokernel_hilbertDegree f j L M a d hM)

theorem generated_tensorDifference_mem_hilbertFiltration (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A)
    (hG : AlgebraicGeometry.SheafCohomology.Projective.FiniteGlobalGenerators.HasFiniteGlobalGenerators L.sheaf) (d : ℕ) (x : KTheory.Projective.CoherentK0 A)
    (hx : x ∈ coherentHilbertFiltration f j (d + 1)) :
    KTheory.Projective.coherentTensorDifference L.sheaf (AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.invertible L) x ∈
      coherentHilbertFiltration f j d := by
  have hh : coherentHilbertFiltration f j (d + 1) ≤
      (coherentHilbertFiltration f j d).comap
        (KTheory.Projective.coherentTensorDifference L.sheaf (AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.invertible L)) := by
    apply (AddSubgroup.closure_le _).mpr
    rintro y ⟨M, hM, rfl⟩
    exact generated_tensorDifference_class_mem_hilbertFiltration f j L hG M d hM
  exact hh hx

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Coherent.HilbertFiltration.ProjectiveK
