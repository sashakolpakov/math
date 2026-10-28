import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.ClosedImmersion
import OAI.AlgebraicGeometry.Resolution.Blowups.Integral.StrictTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlledIdealKernel
import OAI.AlgebraicGeometry.Resolution.Blowups.Integral.IdealSheafProducts

/-! # Strict Comparison -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.StrictComparison.Construction

noncomputable section

/-! The blowup of an integral closed carrier is its actual strict transform in the ambient blowup. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]

local instance (H : X.IdealSheafData) : IsLocallyNoetherian H.subscheme :=
  LocallyOfFiniteType.isLocallyNoetherian H.subschemeι

theorem globalBlowupMap_kernel_eq_strictTransform
    (I H : X.IdealSheafData) (hI : I ≠ ⊥) [IsIntegral H.subscheme]
    (hH : I.comap H.subschemeι ≠ ⊥) :
    letI : IsIso (Data.Construction.globalBlowupToBase I hI ∣_ I.support.compl) :=
      Blowup.Complement.Construction.globalBlowup_supportComplement_isIso I hI
    (FunctorialMap.Construction.globalBlowupMap H.subschemeι I hI hH).ker =
      Integral.StrictTransform.Construction.strictTransformIdeal (Data.Construction.globalBlowupToBase I hI) H I.support.compl := by
  let : IsIso (Data.Construction.globalBlowupToBase I hI ∣_ I.support.compl) :=
    Blowup.Complement.Construction.globalBlowup_supportComplement_isIso I hI
  let V : H.subscheme.Opens := H.subschemeι ⁻¹ᵁ I.support.compl
  have hV : V = (I.comap H.subschemeι).support.compl := by
    rw [Scheme.IdealSheafData.support_comap]
    rfl
  have hn : (V : Set H.subscheme).Nonempty := by
    rw [hV]
    exact Local.Construction.idealSheaf_supportComplement_nonempty (I.comap H.subschemeι) hH
  let : Nonempty V.toScheme := by
    obtain ⟨x, hx⟩ := hn
    exact ⟨⟨x, hx⟩⟩
  let : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  let π := Data.Construction.globalBlowupToBase (I.comap H.subschemeι) hH
  let : IsIso (π ∣_ V) := by
    rw [hV]
    exact Blowup.Complement.Construction.globalBlowup_supportComplement_isIso (I.comap H.subschemeι) hH
  let k : V.toScheme ⟶ Data.Construction.globalBlowup (I.comap H.subschemeι) hH :=
    inv (π ∣_ V) ≫ (π ⁻¹ᵁ V).ι
  have hk : k ≫ π = V.ι := by
    rw [Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  let ρ := FunctorialMap.Construction.globalBlowupMap H.subschemeι I hI hH
  have hρ : ρ ≫ Data.Construction.globalBlowupToBase I hI = π ≫ H.subschemeι :=
    FunctorialMap.Construction.globalBlowupMap_over H.subschemeι I hI hH
  have hunit : I.comap (V.ι ≫ H.subschemeι) = ⊤ := by
    apply ControlledIdealKernel.Construction.idealSheaf_comap_eq_top_of_avoids_support
    intro v hv
    exact v.property hv
  have he : k ≫ ρ = Integral.StrictTransform.Construction.strictTransformOpenMap (Data.Construction.globalBlowupToBase I hI) H I.support.compl := by
    apply Local.Construction.globalBlowup_hom_ext I hI (V.ι ≫ H.subschemeι)
      (by rw [hunit]; exact Integral.IdealSheafProducts.Construction.idealSheaf_top_ne_bot)
    · rw [Category.assoc, hρ, ← Category.assoc, hk]
    · exact Integral.StrictTransform.Construction.strictTransformOpenMap_over _ _ _
  let : IsOpenImmersion k := by dsimp only [k]; infer_instance
  let : IsDominant k := ⟨k.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty k)⟩
  let : IsSchemeTheoreticallyDominant k := IsSchemeTheoreticallyDominant.of_isDominant k
  change ρ.ker = (Integral.StrictTransform.Construction.strictTransformOpenMap (Data.Construction.globalBlowupToBase I hI) H I.support.compl).ker
  rw [← he, Scheme.Hom.ker_comp, k.ker_eq_bot, Scheme.IdealSheafData.map_bot]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.StrictComparison.Construction
