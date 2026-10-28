import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.BlowupClosedKernel
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.StrictComparison
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.BaseChangeCharts
import OAI.AlgebraicGeometry.Resolution.Blowups.ClosedCarrierCenters
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.ComplexNaturality

/-! # Framed Hypersurface Kernel -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global.FramedHypersurfaceKernel.Construction

noncomputable section

/-! Common normal frames identify the native global hypersurface transform with its intrinsic blowup. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]

local instance (H : X.IdealSheafData) : IsLocallyNoetherian H.subscheme :=
  LocallyOfFiniteType.isLocallyNoetherian H.subschemeι

theorem globalBlowupMap_kernel_controlled_on_normal_frame
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (I H : X.IdealSheafData) (hI : I ≠ ⊥)
    [IsIntegral H.subscheme] (hH : I.comap H.subschemeι ≠ ⊥) (U : X.affineOpens) :
    letI := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
    ∀ {ι : Type} [DecidableEq ι] (g : ι → I.ideal U)
      (D : ι → Derivation ℂ Γ(X, U) Γ(X, U)),
      (∀ i j, D i (g j).val = if i = j then 1 else 0) →
      Ideal.span (Set.range (fun i => (g i).val)) = I.ideal U →
      ∀ j : ι, H.ideal U = Ideal.span {(g j).val} →
      (GlobalBlowup.FunctorialMap.Construction.globalBlowupMap H.subschemeι I hI hH).ker.comap (GlobalBlowup.Data.Construction.globalBlowupChart I hI U) =
        (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1).comap (GlobalBlowup.Data.Construction.globalBlowupChart I hI U) := by
  let : Algebra ℂ Γ(X, U) := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
  let : Algebra ℚ Γ(X, U) := ((algebraMap ℂ Γ(X, U)).comp (algebraMap ℚ ℂ)).toAlgebra
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  intro ι _ g D hD hgen j hnormal
  let q := H.subschemeι
  let V : H.subscheme.affineOpens := ⟨q ⁻¹ᵁ U.1, U.2.preimage q⟩
  let φ := (q.appLE U.1 V.1 le_rfl).hom
  have hφ : Function.Surjective φ := by
    change Function.Surjective (H.subschemeι.appLE U.1 (H.subschemeι ⁻¹ᵁ U.1) le_rfl).hom
    rw [Scheme.Hom.appLE_eq_app]
    exact H.subschemeι_app_surjective U
  have hk : RingHom.ker φ = Ideal.span {(g j).val} := by
    change RingHom.ker (H.subschemeι.appLE U.1 (H.subschemeι ⁻¹ᵁ U.1) le_rfl).hom = _
    rw [Scheme.Hom.appLE_eq_app, H.ker_subschemeι_app, hnormal]
  let : IsClosedImmersion (GlobalBlowup.FunctorialMap.Construction.globalBlowupMap q I hI hH) :=
    GlobalBlowup.ClosedImmersion.Construction.globalBlowupMap_isClosedImmersion q I hI hH
  rw [ClosedCarrierCenters.Construction.kernel_comap_of_closed_pullback _ _ _ _ (GlobalBlowup.ClosedImmersion.Construction.globalBlowupMap_affine_isPullback q I hI hH U),
    Affine.BlowupClosedKernel.Construction.affineBlowupMapTo_ker_eq_map, GlobalControlled.BaseChangeCharts.Construction.globalBlowupControlledIdeal_comap_affineBlowup, hnormal]
  exact Affine.BlowupClosedKernel.Construction.framed_closed_hypersurface_affineBlowup_ker (I.ideal U) g D hD hgen j φ hφ hk

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global.FramedHypersurfaceKernel.Construction
