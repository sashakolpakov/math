import OAI.AlgebraicGeometry.Quotients.FiniteDescent.RelativeAffine

/-! # Rigidity Restriction On -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.RigidityRestrictionOn.Construction.RigidityRestriction

noncomputable section

/-! Restricting a section and applying affine rigidity on a neighborhood of the base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X S : Scheme.{u}} (f : X ⟶ S) (e : S ⟶ X) (he : e ≫ f = 𝟙 S)

include he

theorem section_range (V : S.Opens) :
    Set.range (V.ι ≫ e) ⊆ Set.range (f ⁻¹ᵁ V).ι := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨x, rfl⟩
  change (e ≫ f) x.1 ∈ V
  rw [he]
  exact x.2

def section_restrict (V : S.Opens) : V.toScheme ⟶ (f ⁻¹ᵁ V).toScheme :=
  IsOpenImmersion.lift (f ⁻¹ᵁ V).ι (V.ι ≫ e) (section_range f e he V)

@[reassoc]
theorem section_restrict_comp (V : S.Opens) :
    section_restrict f e he V ≫ (f ⁻¹ᵁ V).ι = V.ι ≫ e :=
  IsOpenImmersion.lift_fac _ _ _

theorem section_restrict_comp_base (V : S.Opens) :
    section_restrict f e he V ≫ (f ∣_ V) = 𝟙 _ := by
  apply (cancel_mono V.ι).mp
  rw [Category.assoc, morphismRestrict_ι, section_restrict_comp_assoc,
    he, Category.comp_id, Category.id_comp]

theorem factor_on_open [IsProper f] [Smooth f] [GeometricallyConnected f] [IsReduced X]
    {Y : Scheme.{u}} (h : X ⟶ Y) (U : Y.affineOpens) (V : S.Opens)
    (hV : Set.range ((f ⁻¹ᵁ V).ι ≫ h) ⊆ Set.range U.1.ι) :
    (f ⁻¹ᵁ V).ι ≫ h = (f ⁻¹ᵁ V).ι ≫ f ≫ e ≫ h := by
  let h' := IsOpenImmersion.lift U.1.ι ((f ⁻¹ᵁ V).ι ≫ h) hV
  have hh' : h' ≫ U.1.ι = (f ⁻¹ᵁ V).ι ≫ h := IsOpenImmersion.lift_fac _ _ _
  have : IsAffine U.1.toScheme := U.2
  have H := RelativeAffine.Construction.RelativeAffineRigidity.factor (f ∣_ V) (section_restrict f e he V)
    (section_restrict_comp_base f e he V) h'
  have H' := congrArg (fun g => g ≫ U.1.ι) H
  simp only [Category.assoc] at H'
  rw [hh', section_restrict_comp_assoc, morphismRestrict_ι_assoc] at H'
  exact H'

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.RigidityRestrictionOn.Construction.RigidityRestriction
