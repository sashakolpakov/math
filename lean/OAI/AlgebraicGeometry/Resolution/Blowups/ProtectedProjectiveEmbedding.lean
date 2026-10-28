import OAI.AlgebraicGeometry.Resolution.Blowups.ProtectedPatternProgramExistence
import OAI.AlgebraicGeometry.Resolution.Blowups.ProtectedPatternGeometricInduction
import OAI.AlgebraicGeometry.Resolution.Blowups.ProtectedOpenLiftUniqueness
import OAI.AlgebraicGeometry.Resolution.Blowups.ClosedCarrierCenters

/-! # Protected Projective Embedding -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ProtectedProjectiveEmbedding.Construction

noncomputable section

/-! A smooth projective ambient scheme admits a proper modification with smooth strict image, preserving a prescribed smooth open of an integral closed subscheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem exists_projective_smooth_embeddedStrictTransform
    {X Z : Scheme} [IsIntegral X] [IsIntegral Z] [NoetherianSpace Z]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (A : Foundations.Scheme.SmoothProjective.ProjectivePresentation X f)
    (i : Z ⟶ X) [IsClosedImmersion i] (hi : i.ker ≠ ⊥)
    (O : X.Opens) [Nonempty (i ⁻¹ᵁ O).toScheme]
    [Smooth ((i ⁻¹ᵁ O).ι ≫ (i ≫ f))] :
    ∃ (V : Scheme) (π : V ⟶ X),
      Nonempty (Foundations.Scheme.SmoothProjective.ProjectivePresentation V (π ≫ f)) ∧ IsProper π ∧
      ∃ _ : IsIso (π ∣_ O), Smooth ((EmbeddedStrictTransform.Construction.embeddedStrictOpenMap π i O).imageι ≫ (π ≫ f)) := by
  let : AlgebraicGeometry.IsNoetherian X := A.isNoetherian
  let Z₀ := (i ⁻¹ᵁ O).toScheme
  let i₀ := i ∣_ O
  let : IsIntegral Z₀ := isIntegral_of_isOpenImmersion (i ⁻¹ᵁ O).ι
  let : Nonempty O := by
    obtain ⟨z⟩ := ‹Nonempty (i ⁻¹ᵁ O).toScheme›
    exact ⟨i₀ z⟩
  have hker : i.ker.comap O.ι = i₀.ker :=
    ClosedCarrierCenters.Construction.kernel_comap_of_closed_pullback i i₀ (i ⁻¹ᵁ O).ι O.ι (isPullback_morphismRestrict i O)
  have hground : i₀ ≫ (O.ι ≫ f) = (i ⁻¹ᵁ O).ι ≫ (i ≫ f) := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
  let : Smooth (i₀ ≫ (O.ι ≫ f)) := hground.symm ▸ inferInstance
  let : Smooth ((i.ker.comap O.ι).subschemeι ≫ (O.ι ≫ f)) := by
    rw [hker]
    change Smooth (i₀.imageι ≫ (O.ι ≫ f))
    have he : i₀.imageι = inv i₀.toImage ≫ i₀ :=
      (IsIso.inv_comp_eq i₀.toImage).mpr i₀.toImage_imageι.symm |>.symm
    rw [he, Category.assoc]
    infer_instance
  obtain ⟨Y, g, K, P, hK, ⟨cover⟩⟩ := ProtectedPatternProgramExistence.Construction.exists_global_control_one_with_protected_patterns f i.ker hi O
  obtain ⟨V, π, Q, hπ, hO, q, hq, hsm⟩ := P.exists_smooth_protected_image hK A O Z₀ i₀ hker cover
  let : IsIso (π ∣_ O) := hO
  have hq' : q = EmbeddedStrictTransform.Construction.embeddedStrictOpenMap π i O :=
    ProtectedOpenLiftUniqueness.Construction.eq_embeddedStrictOpenMap_of_over π i O q (hq.trans (morphismRestrict_ι i O))
  refine ⟨V, π, Q, hπ, hO, ?_⟩
  rwa [hq'] at hsm

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ProtectedProjectiveEmbedding.Construction
