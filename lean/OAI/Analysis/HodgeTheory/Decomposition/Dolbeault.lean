import OAI.Analysis.HodgeTheory.Decomposition.Projectors
import OAI.AlgebraicTopology.DeRham.Comparison.ProjectiveComponentPureEquiv
import OAI.AlgebraicTopology.DeRham.Comparison.ManifoldDolbeaultIdentities

/-! # Dolbeault -/

namespace OAI.Analysis.HodgeTheory.Decomposition.Dolbeault.Constructions

noncomputable section

section

/-! Genuine Dolbeault differentials on all projective components and preservation
of the form filtration by the exterior derivative. -/

open scoped BigOperators

variable (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)

def componentDPrime (p q : ℕ) :
    X.componentPureForms p q →ₗ[ℂ] X.componentPureForms (p + 1) q where
  toFun form := (X.componentPureFormsEquiv (p + 1) q).symm
    (fun C => DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime (X.componentPureFormsEquiv p q form C))
  map_add' f g := by
    apply (X.componentPureFormsEquiv (p + 1) q).injective
    funext C
    simp only [LinearEquiv.apply_symm_apply, map_add, Pi.add_apply]
  map_smul' c f := by
    apply (X.componentPureFormsEquiv (p + 1) q).injective
    funext C
    simp only [LinearEquiv.apply_symm_apply, map_smul, Pi.smul_apply, RingHom.id_apply]

def componentDDoublePrime (p q : ℕ) :
    X.componentPureForms p q →ₗ[ℂ] X.componentPureForms p (q + 1) where
  toFun form := (X.componentPureFormsEquiv p (q + 1)).symm
    (fun C => DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime (X.componentPureFormsEquiv p q form C))
  map_add' f g := by
    apply (X.componentPureFormsEquiv p (q + 1)).injective
    funext C
    simp only [LinearEquiv.apply_symm_apply, map_add, Pi.add_apply]
  map_smul' c f := by
    apply (X.componentPureFormsEquiv p (q + 1)).injective
    funext C
    simp only [LinearEquiv.apply_symm_apply, map_smul, Pi.smul_apply, RingHom.id_apply]

@[simp]
theorem componentDPrime_apply (p q : ℕ) (form : X.componentPureForms p q)
    (C : irreducibleComponents X.carrier) :
    (componentDPrime X p q form).val C =
      (DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime (X.componentPureFormsEquiv p q form C)).val := rfl

@[simp]
theorem componentDDoublePrime_apply (p q : ℕ) (form : X.componentPureForms p q)
    (C : irreducibleComponents X.carrier) :
    (componentDDoublePrime X p q form).val C =
      (DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime (X.componentPureFormsEquiv p q form C)).val := rfl

/-- The component-family holomorphic differential squares to zero. -/
theorem componentDPrime_squared (p q : ℕ) (form : X.componentPureForms p q) :
    componentDPrime X (p + 1) q (componentDPrime X p q form) = 0 := by
  apply Subtype.ext
  funext C
  change (DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime (DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime
    (X.componentPureFormsEquiv p q form C))).val = 0
  rw [DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime_squared]
  rfl

/-- The component-family antiholomorphic differential squares to zero. -/
theorem componentDDoublePrime_squared (p q : ℕ) (form : X.componentPureForms p q) :
    componentDDoublePrime X p (q + 1) (componentDDoublePrime X p q form) = 0 := by
  apply Subtype.ext
  funext C
  change (DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime (DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime
    (X.componentPureFormsEquiv p q form C))).val = 0
  rw [DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime_squared]
  rfl

/-- The two genuine component-family differentials anticommute. -/
theorem componentDolbeault_anticommute (p q : ℕ) (form : X.componentPureForms p q) :
    componentDDoublePrime X (p + 1) q (componentDPrime X p q form) +
      componentDPrime X p (q + 1) (componentDDoublePrime X p q form) = 0 := by
  apply Subtype.ext
  funext C
  exact congrArg Subtype.val
    (DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime_dPrime_add_dPrime_dDoublePrime
      (X.componentPureFormsEquiv p q form C))

/-- Equality transport of the total degree of a family of genuine forms. -/
def componentCast {n m : ℕ} (h : n = m) (form : X.componentForms n) : X.componentForms m :=
  h ▸ form

@[simp]
theorem componentCast_apply {n m : ℕ} (h : n = m) (form : X.componentForms n)
    (C : irreducibleComponents X.carrier) :
    componentCast X h form C = DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree h (form C) := by
  cases h
  rfl

/-- Transport only changes the common total-degree index of a pure family. -/
theorem componentCast_pure (p q n : ℕ) (h : p + q = n) (form : X.componentPureForms p q) :
    componentCast X h form.val ∈ Core.Constructions.pureFormsAt X n ⟨(p, q), h⟩ := by
  cases h
  exact form.property

/-- The genuine exterior derivative is the sum of the two neighboring type components. -/
theorem componentDolbeault_sum (p q : ℕ) (form : X.componentPureForms p q) :
    componentCast X (by omega : (p + 1) + q = p + q + 1) (componentDPrime X p q form).val +
      componentCast X (by omega : p + (q + 1) = p + q + 1) (componentDDoublePrime X p q form).val =
        X.componentExteriorDerivative (p + q) form.val := by
  funext C
  simpa only [Pi.add_apply, componentCast_apply, componentDPrime_apply,
    componentDDoublePrime_apply, AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentExteriorDerivative_apply,
    AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentPureFormsEquiv_apply] using
    DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime_add_dDoublePrime (X.componentPureFormsEquiv p q form C)

variable {X}

def advanceHolomorphic {n : ℕ} (i : Core.Constructions.Bidegree n) : Core.Constructions.Bidegree (n + 1) :=
  ⟨(i.val.1 + 1, i.val.2), by have h := i.property; omega⟩

def advanceAntiholomorphic {n : ℕ} (i : Core.Constructions.Bidegree n) : Core.Constructions.Bidegree (n + 1) :=
  ⟨(i.val.1, i.val.2 + 1), by have h := i.property; omega⟩

/-- The derivative of a pure form has only its two neighboring bidegrees. -/
theorem derivative_pure_decomposition (n : ℕ) (i : Core.Constructions.Bidegree n) (form : X.componentForms n)
    (hform : form ∈ Core.Constructions.pureFormsAt X n i) :
    ∃ a b : X.componentForms (n + 1),
      a ∈ Core.Constructions.pureFormsAt X (n + 1) (advanceHolomorphic i) ∧
      b ∈ Core.Constructions.pureFormsAt X (n + 1) (advanceAntiholomorphic i) ∧
      X.componentExteriorDerivative n form = a + b := by
  rcases i with ⟨⟨p, q⟩, hi⟩
  subst n
  let f : X.componentPureForms p q := ⟨form, hform⟩
  refine ⟨componentCast X (by omega : (p + 1) + q = p + q + 1)
      (componentDPrime X p q f).val,
    componentCast X (by omega : p + (q + 1) = p + q + 1)
      (componentDDoublePrime X p q f).val, ?_, ?_, (componentDolbeault_sum X p q f).symm⟩
  · exact componentCast_pure X (p + 1) q (p + q + 1) _ _
  · exact componentCast_pure X p (q + 1) (p + q + 1) _ _

/-- The form filtration really is preserved by the actual exterior derivative. -/
theorem exteriorDerivative_filtered (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ) (r : ℤ) :
    (Core.Constructions.filteredForms X n r).map (X.componentExteriorDerivative n) ≤ Core.Constructions.filteredForms X (n + 1) r := by
  rw [Submodule.map_le_iff_le_comap]
  refine iSup_le fun i => iSup_le fun hri => ?_
  intro form hform
  obtain ⟨a, b, ha, hb, hab⟩ := derivative_pure_decomposition n i form hform
  change X.componentExteriorDerivative n form ∈ Core.Constructions.filteredForms X (n + 1) r
  rw [hab]
  apply Submodule.add_mem
  · apply Submodule.mem_iSup_of_mem (advanceHolomorphic i)
    apply Submodule.mem_iSup_of_mem (show r ≤ ((advanceHolomorphic i).val.1 : ℤ) by
      dsimp [advanceHolomorphic]; omega)
    exact ha
  · apply Submodule.mem_iSup_of_mem (advanceAntiholomorphic i)
    apply Submodule.mem_iSup_of_mem (show r ≤ ((advanceAntiholomorphic i).val.1 : ℤ) from hri)
    exact hb

end

/-! Exact projection criteria for the form filtration and the pure exact
obstruction to splitting a closed filtered representative. -/

open scoped BigOperators

variable (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)

theorem componentAction_pure (n : ℕ) (i : Core.Constructions.Bidegree n) (form : X.componentForms n)
    (hform : form ∈ Core.Constructions.pureFormsAt X n i) (z : ℂˣ) :
    Types.Constructions.componentAction X n z form = Types.Constructions.inverseTypeCharacter i z • form := by
  funext C
  simpa only [Types.Constructions.componentAction_apply, Types.Constructions.inverseTypeCharacter, DifferentialForms.Manifold.Bidegree.bidegreeCharacter_inv,
    Pi.smul_apply] using (Core.Constructions.mem_pureFormsAt_iff_action X n i form).mp hform C z

theorem componentProjection_identity (n : ℕ) (i : Core.Constructions.Bidegree n) (form : X.componentForms n)
    (hform : form ∈ Core.Constructions.pureFormsAt X n i) : Projectors.Constructions.componentProjection X n i form = form :=
  Projectors.Constructions.spectralProjector_identity _ _ _ i form (componentAction_pure X n i form hform)

theorem componentProjection_other (n : ℕ) (i j : Core.Constructions.Bidegree n) (hij : i ≠ j)
    (form : X.componentForms n) (hform : form ∈ Core.Constructions.pureFormsAt X n j) :
    Projectors.Constructions.componentProjection X n i form = 0 :=
  Projectors.Constructions.spectralProjector_zero _ _ _ i j hij form (componentAction_pure X n j form hform)

theorem componentProjection_self (n : ℕ) (i : Core.Constructions.Bidegree n) (form : X.componentForms n) :
    Projectors.Constructions.componentProjection X n i (Projectors.Constructions.componentProjection X n i form) = Projectors.Constructions.componentProjection X n i form :=
  componentProjection_identity X n i _ (Projectors.Constructions.componentProjection_pure X n i form)

/-- Every type strictly below the filtration threshold vanishes. -/
theorem projection_below_filtration (n : ℕ) (r : ℤ) (form : X.componentForms n)
    (hform : form ∈ Core.Constructions.filteredForms X n r) (i : Core.Constructions.Bidegree n) (hi : (i.val.1 : ℤ) < r) :
    Projectors.Constructions.componentProjection X n i form = 0 := by
  have hle : Core.Constructions.filteredForms X n r ≤ LinearMap.ker (Projectors.Constructions.componentProjection X n i) := by
    refine iSup_le fun j => iSup_le fun hj => ?_
    intro f hf
    have hij : i ≠ j := by
      intro he
      subst j
      exact (not_le_of_gt hi) hj
    exact componentProjection_other X n i j hij f hf
  exact hle hform

/-- A form lies in the filtration exactly when all lower-type projections vanish. -/
theorem mem_filteredForms_iff_projections (n : ℕ) (r : ℤ) (form : X.componentForms n) :
    form ∈ Core.Constructions.filteredForms X n r ↔
      ∀ i : Core.Constructions.Bidegree n, (i.val.1 : ℤ) < r → Projectors.Constructions.componentProjection X n i form = 0 := by
  constructor
  · exact projection_below_filtration X n r form
  · intro h
    rw [← Projectors.Constructions.sum_componentProjection X n form]
    apply Submodule.sum_mem
    intro i _
    by_cases hi : r ≤ (i.val.1 : ℤ)
    · apply Submodule.mem_iSup_of_mem i
      apply Submodule.mem_iSup_of_mem hi
      exact Projectors.Constructions.componentProjection_pure X n i form
    · rw [h i (lt_of_not_ge hi)]
      exact Submodule.zero_mem _

/-- The effective de Rham filtration is exhaustive at nonpositive indices. -/
theorem filteredForms_eq_top_of_nonpos (n : ℕ) (r : ℤ) (hr : r ≤ 0) :
    Core.Constructions.filteredForms X n r = ⊤ := by
  apply top_unique
  intro form _
  rw [mem_filteredForms_iff_projections]
  intro i hi
  have hn : (0 : ℤ) ≤ i.val.1 := Nat.cast_nonneg _
  exact False.elim ((not_lt_of_ge (hr.trans hn)) hi)

theorem deRhamFiltration_eq_top_of_nonpos (n : ℕ) (r : ℤ) (hr : r ≤ 0) :
    Core.Constructions.deRhamFiltrationBetti X n r = ⊤ := by
  unfold Core.Constructions.deRhamFiltrationBetti
  rw [filteredForms_eq_top_of_nonpos X n r hr, Submodule.comap_top, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (Core.Constructions.closedFormBettiClass_surjective X n)

theorem bidegree_eq_of_first {n : ℕ} (i j : Core.Constructions.Bidegree n) (h : i.val.1 = j.val.1) : i = j := by
  apply Subtype.ext
  apply Prod.ext h
  have hi := i.property
  have hj := j.property
  omega

/-- Removing the lowest type raises the form filtration by one. -/
theorem subtract_lowest_projection_filtered (n : ℕ) (i : Core.Constructions.Bidegree n) (form : X.componentForms n)
    (hform : form ∈ Core.Constructions.filteredForms X n (i.val.1 : ℤ)) :
    form - Projectors.Constructions.componentProjection X n i form ∈ Core.Constructions.filteredForms X n ((i.val.1 : ℤ) + 1) := by
  rw [mem_filteredForms_iff_projections]
  intro j hj
  rw [map_sub]
  by_cases hji : j = i
  · subst j
    rw [componentProjection_self, sub_self]
  · have hfirst : j.val.1 ≠ i.val.1 := fun he => hji (bidegree_eq_of_first j i he)
    have hlt : (j.val.1 : ℤ) < i.val.1 := by omega
    rw [projection_below_filtration X n _ form hform j hlt,
      componentProjection_other X n j i hji _ (Projectors.Constructions.componentProjection_pure X n i form), sub_self]

/-- A pure form below a filtration threshold that nevertheless lies in that filtration is zero. -/
theorem pure_filtered_eq_zero (n : ℕ) (r : ℤ) (i : Core.Constructions.Bidegree n) (form : X.componentForms n)
    (hpure : form ∈ Core.Constructions.pureFormsAt X n i) (hfiltered : form ∈ Core.Constructions.filteredForms X n r)
    (hi : (i.val.1 : ℤ) < r) : form = 0 := by
  rw [← componentProjection_identity X n i form hpure]
  exact projection_below_filtration X n r form hfiltered i hi

/-- For a closed filtered form, the derivative of its lowest-type component has only
one raised type. This is the concrete obstruction used in the correction step. -/
theorem derivative_lowest_projection_pure (n : ℕ) (i : Core.Constructions.Bidegree n)
    (form : X.componentClosedForms n)
    (hform : form.val ∈ Core.Constructions.filteredForms X n (i.val.1 : ℤ)) :
    X.componentExteriorDerivative n (Projectors.Constructions.componentProjection X n i form.val) ∈
      Core.Constructions.pureFormsAt X (n + 1) (advanceHolomorphic i) := by
  let a := Projectors.Constructions.componentProjection X n i form.val
  have hrem := subtract_lowest_projection_filtered X n i form.val hform
  have hdr := exteriorDerivative_filtered X n ((i.val.1 : ℤ) + 1)
    (Submodule.mem_map_of_mem hrem)
  have hclosed : X.componentExteriorDerivative n form.val = 0 := form.property
  rw [map_sub, hclosed, zero_sub] at hdr
  have hda : X.componentExteriorDerivative n a ∈ Core.Constructions.filteredForms X (n + 1) ((i.val.1 : ℤ) + 1) :=
    (Submodule.neg_mem_iff _).mp hdr
  obtain ⟨u, v, hu, hv, hd⟩ := derivative_pure_decomposition n i a (Projectors.Constructions.componentProjection_pure X n i form.val)
  have huF : u ∈ Core.Constructions.filteredForms X (n + 1) ((i.val.1 : ℤ) + 1) := by
    apply Submodule.mem_iSup_of_mem (advanceHolomorphic i)
    apply Submodule.mem_iSup_of_mem (show (i.val.1 : ℤ) + 1 ≤ ((advanceHolomorphic i).val.1 : ℤ) by
      simp [advanceHolomorphic])
    exact hu
  have hvF : v ∈ Core.Constructions.filteredForms X (n + 1) ((i.val.1 : ℤ) + 1) := by
    have h := (Core.Constructions.filteredForms X (n + 1) ((i.val.1 : ℤ) + 1)).sub_mem hda huF
    rwa [hd, add_sub_cancel_left] at h
  have hv0 : v = 0 := pure_filtered_eq_zero X (n + 1) _ (advanceAntiholomorphic i) v hv hvF
    (by simp [advanceAntiholomorphic])
  rwa [hd, hv0, add_zero]

/-- The obstruction is a genuine closed form. -/
def lowestObstruction (n : ℕ) (i : Core.Constructions.Bidegree n) (form : X.componentClosedForms n) :
    X.componentClosedForms (n + 1) :=
  ⟨X.componentExteriorDerivative n (Projectors.Constructions.componentProjection X n i form.val),
    X.componentExteriorDerivative_squared n (Projectors.Constructions.componentProjection X n i form.val)⟩

/-- Its de Rham class is zero, with the explicit smooth primitive retained. -/
theorem lowestObstruction_class_zero (n : ℕ) (i : Core.Constructions.Bidegree n) (form : X.componentClosedForms n) :
    X.componentDeRhamClass (n + 1) (lowestObstruction X n i form) = 0 := by
  rw [X.componentDeRhamClass_eq_zero_iff]
  exact ⟨Projectors.Constructions.componentProjection X n i form.val, rfl⟩

end

end OAI.Analysis.HodgeTheory.Decomposition.Dolbeault.Constructions
