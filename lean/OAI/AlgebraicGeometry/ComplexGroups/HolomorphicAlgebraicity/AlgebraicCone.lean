import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ParametrizedConeEquation
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.LinearPolynomial

/-! # Algebraic Cone -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.AlgebraicCone.Constructions.Cone

noncomputable section

/-!
# Finite homogeneous equations for a parametrized analytic cone

The scalar-image equations separate every point outside the cone: a linear
functional separates that point from its finite normalization fiber. The
Hilbert basis theorem reduces these homogeneous equations to finitely many.
-/

open Set _root_.MvPolynomial

theorem finite_equations_of_homogeneous_separation
    {ι : Type*} [Finite ι] {S : Set (ι → ℂ)}
    (hsep : ∀ x ∉ S, ∃ q : MvPolynomial ι ℂ,
      (∃ d, q.IsHomogeneous d) ∧ (∀ v ∈ S, eval v q = 0) ∧ eval x q ≠ 0) :
    ∃ Q : Finset (MvPolynomial ι ℂ),
      (∀ q ∈ Q, ∃ d, q.IsHomogeneous d) ∧ S = {v | ∀ q ∈ Q, eval v q = 0} := by
  classical
  let H : Set (MvPolynomial ι ℂ) :=
    {q | (∃ d, q.IsHomogeneous d) ∧ ∀ v ∈ S, eval v q = 0}
  obtain ⟨Q, hQ, hspan⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset (R := MvPolynomial ι ℂ) H).mp
      (IsNoetherian.noetherian _)
  change Ideal.span H = Ideal.span (Q : Set (MvPolynomial ι ℂ)) at hspan
  refine ⟨Q, fun q hq => (hQ hq).1, ?_⟩
  ext x
  constructor
  · intro hx q hq
    exact (hQ hq).2 x hx
  · intro hx
    by_contra hxS
    obtain ⟨q, hqh, hqS, hqx⟩ := hsep x hxS
    have hker : Ideal.span (Q : Set (MvPolynomial ι ℂ)) ≤ RingHom.ker (eval x) := by
      apply Ideal.span_le.mpr
      intro p hp
      exact hx p hp
    apply hqx
    apply hker
    rw [← hspan]
    exact Ideal.subset_span ⟨hqh, hqS⟩

theorem exists_homogeneous_separator_of_parametrized_cone
    {E ι : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {n : ℕ} (hn : 0 < n)
    (hdim : Module.finrank ℂ E = Module.finrank ℂ (Fin n → ℂ))
    {S : Set (ι → ℂ)} (hzero : 0 ∈ S) (hS : IsClosed S)
    (hcone : ∀ (c : ℂ) ⦃v⦄, v ∈ S → c • v ∈ S)
    (hlocal : ∀ v ∈ S, v ≠ 0 → ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S v)
    (L : (ι → ℂ) →L[ℂ] (Fin n → ℂ)) (hker : ∀ v ∈ S, L v = 0 → v = 0)
    (hfinite : ∀ y, {v | v ∈ S ∧ L v = y}.Finite) (hsurj : L '' S = univ)
    (hparam : ∀ p ∈ S, p ≠ 0 → ∃ (O : Set (ι → ℂ)) (U : Set E) (φ : E → (ι → ℂ)),
      IsOpen O ∧ p ∈ O ∧ IsOpen U ∧ DifferentiableOn ℂ φ U ∧
      S ∩ O ⊆ φ '' U ∧ MapsTo φ U S ∧ InjOn φ U)
    {x : ι → ℂ} (hx : x ∉ S) :
    ∃ q : MvPolynomial ι ℂ,
      (∃ d, q.IsHomogeneous d) ∧ (∀ v ∈ S, eval v q = 0) ∧ eval x q ≠ 0 := by
  obtain ⟨ℓ, hℓ⟩ := LinearPolynomial.Constructions.Cone.exists_linear_functional_separating_finite_set (hfinite (L x))
    (show x ∉ {v | v ∈ S ∧ L v = L x} from fun h => hx h.1)
  obtain ⟨d, F, _, hF, _, heq, _⟩ := ParametrizedConeEquation.Constructions.Cone.exists_full_homogeneous_coordinate_equation
    hn hdim hzero hS hcone hlocal L hker hfinite hsurj hparam ℓ
  let C : ((Fin n → ℂ) × ℂ) →L[ℂ] (Option (Fin n) → ℂ) :=
    { toFun := fun p => ConeFiberEquation.Constructions.Cone.fiberCoordinates p.1 p.2
      map_add' := by intro p q; ext i; cases i <;> rfl
      map_smul' := by intro c p; ext i; cases i <;> rfl
      cont := ParametrizedConeEquation.Constructions.Cone.continuous_fiberCoordinates }
  obtain ⟨q, hq, hqeval⟩ := LinearPolynomial.Constructions.Cone.exists_homogeneous_linear_substitution (C.comp (L.prod ℓ)) hF
  have hev (v : ι → ℂ) : eval v q = eval (ConeFiberEquation.Constructions.Cone.fiberCoordinates (L v) (ℓ v)) F := hqeval v
  refine ⟨q, ⟨d, hq⟩, ?_, ?_⟩
  · intro v hv
    rw [hev]
    exact (heq (L v) (ℓ v)).mp ⟨v, hv, rfl⟩
  · intro hqx
    rw [hev] at hqx
    obtain ⟨v, hv, hvx⟩ := (heq (L x) (ℓ x)).mpr hqx
    exact hℓ v ⟨hv, congrArg Prod.fst hvx⟩ (congrArg Prod.snd hvx).symm

theorem finite_equations_of_parametrized_cone
    {E ι : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {n : ℕ} (hn : 0 < n)
    (hdim : Module.finrank ℂ E = Module.finrank ℂ (Fin n → ℂ))
    {S : Set (ι → ℂ)} (hzero : 0 ∈ S) (hS : IsClosed S)
    (hcone : ∀ (c : ℂ) ⦃v⦄, v ∈ S → c • v ∈ S)
    (hlocal : ∀ v ∈ S, v ≠ 0 → ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S v)
    (L : (ι → ℂ) →L[ℂ] (Fin n → ℂ)) (hker : ∀ v ∈ S, L v = 0 → v = 0)
    (hfinite : ∀ y, {v | v ∈ S ∧ L v = y}.Finite) (hsurj : L '' S = univ)
    (hparam : ∀ p ∈ S, p ≠ 0 → ∃ (O : Set (ι → ℂ)) (U : Set E) (φ : E → (ι → ℂ)),
      IsOpen O ∧ p ∈ O ∧ IsOpen U ∧ DifferentiableOn ℂ φ U ∧
      S ∩ O ⊆ φ '' U ∧ MapsTo φ U S ∧ InjOn φ U) :
    ∃ Q : Finset (MvPolynomial ι ℂ),
      (∀ q ∈ Q, ∃ d, q.IsHomogeneous d) ∧ S = {v | ∀ q ∈ Q, eval v q = 0} := by
  apply finite_equations_of_homogeneous_separation
  intro x hx
  exact exists_homogeneous_separator_of_parametrized_cone
    hn hdim hzero hS hcone hlocal L hker hfinite hsurj hparam hx

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.AlgebraicCone.Constructions.Cone
