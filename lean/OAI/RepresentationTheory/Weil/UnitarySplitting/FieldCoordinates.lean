import OAI.RepresentationTheory.Weil.UnitarySplitting.RealFourierUnitary

/-! # Field Coordinates -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.FieldCoordinates.Construction

noncomputable section

/-! Transport of test functions and Weyl operators through a continuous
field isomorphism. Haar measures may differ by a positive scalar, which
cancels when transporting energy-preserving operators. -/

open _root_.MeasureTheory
open scoped BigOperators NNReal

def coordinateFieldEquiv {A B : Type} [NormedField A] [NormedField B]
    (I : Type) (e : A ≃+* B) (he : Continuous e) (hei : Continuous e.symm) :
    (I → A) ≃ₜ+ (I → B) where
  toFun x i := e (x i)
  invFun x i := e.symm (x i)
  left_inv x := by funext i; exact e.symm_apply_apply (x i)
  right_inv x := by funext i; exact e.apply_symm_apply (x i)
  map_add' x y := by funext i; exact map_add e (x i) (y i)
  continuous_toFun := continuous_pi (fun i => he.comp (continuous_apply i))
  continuous_invFun := continuous_pi (fun i => hei.comp (continuous_apply i))

theorem schwartzBruhat_comp_cross_addEquiv
    {A B : Type} [NormedField A] [NormedField B] {m n : ℕ}
    (e : Local.FunctionsMetaplectic.Construction.Position A m ≃ₜ+ Local.FunctionsMetaplectic.Construction.Position B n)
    {f : Local.FunctionsMetaplectic.Construction.Position B n → ℂ} (hf : f ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat B n) : f ∘ e ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat A m := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      rcases hf with hf | ⟨r, a, φ, rfl⟩
      · exact Local.FunctionsMetaplectic.Construction.compact_locallyConstant_mem
          (hf.1.comp_continuous e.continuous) (hf.2.comp_homeomorph e.toHomeomorph)
      · exact Local.FunctionsMetaplectic.Construction.schwartz_coordinate_mem (a.trans e.symm) φ
  | zero => exact (Local.FunctionsMetaplectic.Construction.schwartzBruhat A m).zero_mem
  | add f g _ _ hf hg => exact (Local.FunctionsMetaplectic.Construction.schwartzBruhat A m).add_mem hf hg
  | smul c f _ hf => exact (Local.FunctionsMetaplectic.Construction.schwartzBruhat A m).smul_mem c hf

def crossFieldTestEquiv
    {A B : Type} [NormedField A] [NormedField B] {m n : ℕ}
    (e : Local.FunctionsMetaplectic.Construction.Position A m ≃ₜ+ Local.FunctionsMetaplectic.Construction.Position B n) : Local.FunctionsMetaplectic.Construction.schwartzBruhat B n ≃ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat A m where
  toFun f := ⟨f.val ∘ e, schwartzBruhat_comp_cross_addEquiv e f.property⟩
  invFun f := ⟨f.val ∘ e.symm, schwartzBruhat_comp_cross_addEquiv e.symm f.property⟩
  left_inv f := by ext x; simp
  right_inv f := by ext x; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem heisenberg_field_coordinates
    {A B : Type} [NormedField A] [NormedField B] {d : ℕ}
    (e : A ≃+* B) (he : Continuous e) (hei : Continuous e.symm)
    (ψ : AddChar B ℂ) (v : Local.FunctionsMetaplectic.Construction.PhaseSpace B d) (f : Local.FunctionsMetaplectic.Construction.Position B d → ℂ) :
    (fun x => Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v f (coordinateFieldEquiv (Fin d) e he hei x)) =
      Local.FunctionsMetaplectic.Construction.heisenbergFunction (ψ.compAddMonoidHom e.toAddEquiv.toAddMonoidHom)
        ((coordinateFieldEquiv (Fin d ⊕ Fin d) e he hei).symm v)
        (fun x => f (coordinateFieldEquiv (Fin d) e he hei x)) := by
  funext x
  change ψ (∑ i, v (Sum.inr i) * (e (x i) - v (Sum.inl i) / 2)) *
      f (fun i => e (x i) - v (Sum.inl i)) =
    ψ (e (∑ i, e.symm (v (Sum.inr i)) * (x i - e.symm (v (Sum.inl i)) / 2))) *
      f (fun i => e (x i - e.symm (v (Sum.inl i))))
  simp only [map_sum, map_mul, map_sub, map_div₀, map_ofNat, e.apply_symm_apply]

variable {A B : Type} [NormedField A] [NormedField B]
variable [LocallyCompactSpace A] [LocallyCompactSpace B]
variable [MeasurableSpace A] [MeasurableSpace B] [BorelSpace A] [BorelSpace B]
variable [SecondCountableTopology A] [SecondCountableTopology B] {m n : ℕ}

theorem crossFieldTestEquiv_energy_ratio (e : Local.FunctionsMetaplectic.Construction.Position A m ≃ₜ+ Local.FunctionsMetaplectic.Construction.Position B n) :
    ∃ r : ℝ≥0, ∀ f : Local.FunctionsMetaplectic.Construction.schwartzBruhat B n,
      Local.FunctionsMetaplectic.Construction.l2Energy B n f = r * Local.FunctionsMetaplectic.Construction.l2Energy A m (crossFieldTestEquiv e f) := by
  let μ := Weak.Construction.referencePositionMeasure B n
  let ν := μ.map e.symm
  let : ν.IsAddHaarMeasure := e.symm.isAddHaarMeasure_map μ
  have hν := Measure.isAddLeftInvariant_eq_smul_of_regular ν (Weak.Construction.referencePositionMeasure A m)
  refine ⟨Measure.addHaarScalarFactor ν (Weak.Construction.referencePositionMeasure A m), fun f => ?_⟩
  have heq : Local.FunctionsMetaplectic.Construction.l2Energy B n f = ∫ x, ‖(crossFieldTestEquiv e f).val x‖ ^ 2 ∂ν := by
    change Local.FunctionsMetaplectic.Construction.l2Energy B n f = ∫ x, ‖(crossFieldTestEquiv e f).val x‖ ^ 2
      ∂μ.map e.symm.toHomeomorph
    rw [e.symm.toHomeomorph.isClosedEmbedding.integral_map]
    change (∫ x, ‖f.val x‖ ^ 2 ∂μ) = ∫ x, ‖f.val (e (e.symm x))‖ ^ 2 ∂μ
    simp only [e.apply_symm_apply]
  rw [heq]
  conv_lhs => rw [hν, integral_smul_nnreal_measure]
  rfl

theorem crossFieldTestEquiv_transport_unitary
    (e : Local.FunctionsMetaplectic.Construction.Position A m ≃ₜ+ Local.FunctionsMetaplectic.Construction.Position B n)
    (U : Local.FunctionsMetaplectic.Construction.schwartzBruhat A m ≃ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat A m)
    (hU : ∀ f, Local.FunctionsMetaplectic.Construction.l2Energy A m (U f) = Local.FunctionsMetaplectic.Construction.l2Energy A m f) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat B n) :
    Local.FunctionsMetaplectic.Construction.l2Energy B n (((crossFieldTestEquiv e).trans U).trans (crossFieldTestEquiv e).symm f) =
      Local.FunctionsMetaplectic.Construction.l2Energy B n f := by
  obtain ⟨r, hr⟩ := crossFieldTestEquiv_energy_ratio e
  rw [hr, hr f]
  change r * Local.FunctionsMetaplectic.Construction.l2Energy A m ((crossFieldTestEquiv e)
    ((crossFieldTestEquiv e).symm (U (crossFieldTestEquiv e f)))) = _
  rw [LinearEquiv.apply_symm_apply, hU]

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.FieldCoordinates.Construction
