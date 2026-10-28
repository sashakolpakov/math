import OAI.AlgebraicTopology.DeRham.Comparison.ManifoldDolbeaultIdentities
import OAI.AlgebraicTopology.DeRham.Comparison.ClosedPureManifoldNumerator
import OAI.AlgebraicTopology.DeRham.Comparison.QuotientImage

/-! # Manifold Hodge Quotient -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.ManifoldHodgeQuotient

noncomputable section

/-!
# The literal closed-pure-form quotient in the Clay statement

The denominator in positive bidegree is the image of the actual global
operator d′d″ on pure forms. Its closedness and exactness are proved from
the genuine Dolbeault identities. If either bidegree is zero the denominator
is zero, since there are no forms of negative bidegree.

The resulting quotient maps naturally to actual de Rham cohomology, and its
image is exactly the existing subspace represented by closed pure forms.
This image equality does not assert a d′d″ lemma or a Hodge decomposition.
-/

open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] (M : Type*) [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M]

/-- The actual d′d″ operator takes values in genuine closed pure forms. -/
def manifoldDDbarToClosedPure (p q : ℕ) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M p q →ₗ[ℂ] ManifoldPureClasses.pureClosedManifoldForms E M (p + 1) (q + 1) where
  toFun form :=
    ⟨⟨(Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrimeDoublePrime (E := E) (M := M) (p := p) (q := q) form).val,
      Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.d_dPrimeDoublePrime (E := E) (M := M) (p := p) (q := q) form⟩,
      (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrimeDoublePrime (E := E) (M := M) (p := p) (q := q) form).property⟩
  map_add' form other := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun a : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M (p + 1) (q + 1) => a.val) (map_add
      (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrimeDoublePrime (E := E) (M := M) (p := p) (q := q)) form other)
  map_smul' a form := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun b : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M (p + 1) (q + 1) => b.val) (map_smul
      (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrimeDoublePrime (E := E) (M := M) (p := p) (q := q)) a form)

@[simp]
theorem manifoldDDbarToClosedPure_val (p q : ℕ) (form : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M p q) :
    (manifoldDDbarToClosedPure E M p q form).val.val =
      (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrimeDoublePrime (E := E) (M := M) (p := p) (q := q) form).val := rfl

/-- The literal d′d″ denominator, with no incoming form at a negative bidegree. -/
def manifoldDDbarBoundaries : (p q : ℕ) → Submodule ℂ (ManifoldPureClasses.pureClosedManifoldForms E M p q)
  | 0, _ => ⊥
  | _ + 1, 0 => ⊥
  | p + 1, q + 1 => LinearMap.range (manifoldDDbarToClosedPure E M p q)

@[simp]
theorem manifoldDDbarBoundaries_zero_left (q : ℕ) :
    manifoldDDbarBoundaries E M 0 q = ⊥ := rfl

@[simp]
theorem manifoldDDbarBoundaries_zero_right (p : ℕ) :
    manifoldDDbarBoundaries E M p 0 = ⊥ := by
  cases p <;> rfl

@[simp]
theorem manifoldDDbarBoundaries_succ_succ (p q : ℕ) :
    manifoldDDbarBoundaries E M (p + 1) (q + 1) =
      LinearMap.range (manifoldDDbarToClosedPure E M p q) := rfl

/-- Denominator membership means being the actual d′d″ of a genuine pure form. -/
theorem mem_manifoldDDbarBoundaries_succ_succ (p q : ℕ)
    (form : ManifoldPureClasses.pureClosedManifoldForms E M (p + 1) (q + 1)) :
    form ∈ manifoldDDbarBoundaries E M (p + 1) (q + 1) ↔
      ∃ primitive : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M p q,
        (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrimeDoublePrime (E := E) (M := M) (p := p) (q := q) primitive).val =
          form.val.val := by
  constructor
  · rintro ⟨primitive, hprimitive⟩
    exact ⟨primitive, congrArg (fun a => a.val.val) hprimitive⟩
  · rintro ⟨primitive, hprimitive⟩
    exact ⟨primitive, Subtype.ext (Subtype.ext hprimitive)⟩

/-- Every actual d′d″ boundary is an actual globally exact form. -/
theorem manifoldDDbarBoundaries_le_exact (p q : ℕ) :
    manifoldDDbarBoundaries E M p q ≤
      (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldExactClosedForms E M (p + q)).comap
        (ManifoldPureClasses.pureClosedManifoldForms E M p q).subtype := by
  cases p with
  | zero => exact bot_le
  | succ p =>
      cases q with
      | zero => exact bot_le
      | succ q =>
          rintro _ ⟨primitive, rfl⟩
          apply (Analysis.DifferentialForms.Manifold.ManifoldDeRham.mem_manifoldExactClosedForms_iff E M _ _).mpr
          exact Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrimeDoublePrime_exact (E := E) (M := M) (p := p) (q := q)
            primitive

/-- The proved exactness kills the concrete denominator under the actual de Rham class map. -/
theorem manifoldDDbarBoundaries_le_ker_class (p q : ℕ) :
    manifoldDDbarBoundaries E M p q ≤ LinearMap.ker (ManifoldPureClasses.manifoldPureFormClass E M p q) := by
  intro form hform
  change ManifoldPureClasses.manifoldPureFormClass E M p q form = 0
  apply (ManifoldPureClasses.manifoldPureFormClass_eq_zero_iff E M p q form).mpr
  exact (Analysis.DifferentialForms.Manifold.ManifoldDeRham.mem_manifoldExactClosedForms_iff E M (p + q) form.val).mp
    (manifoldDDbarBoundaries_le_exact E M p q hform)

/-- The Clay closed-(p,q)-forms modulo d′d″ quotient, with its literal denominator. -/
abbrev manifoldHodgeQuotient (p q : ℕ) :=
  ManifoldPureClasses.pureClosedManifoldForms E M p q ⧸ manifoldDDbarBoundaries E M p q

/-- The canonical projection of a genuine closed pure form to the literal quotient. -/
def manifoldHodgeProjection (p q : ℕ) :
    ManifoldPureClasses.pureClosedManifoldForms E M p q →ₗ[ℂ] manifoldHodgeQuotient E M p q :=
  (manifoldDDbarBoundaries E M p q).mkQ

/-- The natural map to the literal closed-forms modulo exact-forms quotient. -/
def manifoldHodgeToFormQuotient (p q : ℕ) :
    manifoldHodgeQuotient E M p q →ₗ[ℂ] Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormQuotient E M (p + q) :=
  (manifoldDDbarBoundaries E M p q).mapQ (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldExactClosedForms E M (p + q))
    (ManifoldPureClasses.pureClosedManifoldForms E M p q).subtype (manifoldDDbarBoundaries_le_exact E M p q)

/-- The natural map to actual de Rham cohomology, descended using proved exactness. -/
def manifoldHodgeToDeRham (p q : ℕ) :
    manifoldHodgeQuotient E M p q →ₗ[ℂ] Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamCohomology E M (p + q) :=
  (manifoldDDbarBoundaries E M p q).liftQ (ManifoldPureClasses.manifoldPureFormClass E M p q)
    (manifoldDDbarBoundaries_le_ker_class E M p q)

@[simp]
theorem manifoldHodgeToDeRham_projection (p q : ℕ) (form : ManifoldPureClasses.pureClosedManifoldForms E M p q) :
    manifoldHodgeToDeRham E M p q (manifoldHodgeProjection E M p q form) =
      ManifoldPureClasses.manifoldPureFormClass E M p q form := rfl

/-- The two natural maps are identified by the proved de Rham quotient isomorphism. -/
theorem manifoldHodgeToDeRham_eq_quotient (p q : ℕ) :
    manifoldHodgeToDeRham E M p q =
      (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormQuotientIso E M (p + q)).toLinearEquiv.symm.toLinearMap.comp
        (manifoldHodgeToFormQuotient E M p q) := by
  apply LinearMap.ext
  intro x
  obtain ⟨form, rfl⟩ := (manifoldDDbarBoundaries E M p q).mkQ_surjective x
  rfl

/-- The literal quotient has exactly the established pure image in the form quotient. -/
theorem range_manifoldHodgeToFormQuotient (p q : ℕ) :
    LinearMap.range (manifoldHodgeToFormQuotient E M p q) =
      ManifoldPureClasses.manifoldPureQuotientImage E M p q :=
  QuotientImage.range_submodule_quotient_map (ManifoldPureClasses.pureClosedManifoldForms E M p q)
    (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldExactClosedForms E M (p + q)) (manifoldDDbarBoundaries E M p q)
    (manifoldDDbarBoundaries_le_exact E M p q)

/-- The literal quotient has exactly the established pure de Rham image. -/
theorem range_manifoldHodgeToDeRham (p q : ℕ) :
    LinearMap.range (manifoldHodgeToDeRham E M p q) = ManifoldPureClasses.manifoldPureDeRhamImage E M p q := by
  rw [manifoldHodgeToDeRham, Submodule.range_liftQ, ManifoldPureClasses.range_manifoldPureFormClass]

end

end OAI.AlgebraicTopology.DeRham.Comparison.ManifoldHodgeQuotient
