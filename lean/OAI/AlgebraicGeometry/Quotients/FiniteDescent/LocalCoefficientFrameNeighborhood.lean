import OAI.AlgebraicGeometry.Quotients.FiniteDescent.FieldModelFrameNeighborhood
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.CoefficientUnitExactness
import Mathlib.AlgebraicGeometry.Stalk

/-! # Local Coefficient Frame Neighborhood -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.LocalCoefficientFrameNeighborhood.Construction.ModelFrameNeighborhood

noncomputable section

/-! On an affine scheme with local coefficient ring, a neighborhood of
the actual coefficient-residue point is the whole scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Modules
universe u

theorem coefficientResidue_open_eq_top
    (S : Scheme.{u}) [IsAffine S] [IsLocalRing Γ(S, ⊤)]
    (V : S.Opens)
    (hV : AbelianModuli.ReferenceFamily.Affine.CoefficientUnitExactness.coefficientFieldPoint S (IsLocalRing.ResidueField Γ(S, ⊤))
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField Γ(S, ⊤))) ∈ V) : V = ⊤ := by
  let a := inv S.toSpecΓ
  have hq : AbelianModuli.ReferenceFamily.Affine.CoefficientUnitExactness.coefficientFieldPoint S (IsLocalRing.ResidueField Γ(S, ⊤))
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField Γ(S, ⊤))) =
        a (IsLocalRing.closedPoint Γ(S, ⊤)) := by
    change a (PrimeSpectrum.comap (IsLocalRing.residue Γ(S, ⊤))
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField Γ(S, ⊤)))) = _
    rw [IsLocalRing.PrimeSpectrum.comap_residue]
  have ha : a (IsLocalRing.closedPoint Γ(S, ⊤)) ∈ V := hq ▸ hV
  have htop : a ⁻¹ᵁ V = ⊤ := Scheme.preimage_eq_top_of_closedPoint_mem a ha
  apply top_unique
  intro x _
  have hx : S.toSpecΓ x ∈ a ⁻¹ᵁ V := by rw [htop]; trivial
  change a (S.toSpecΓ x) ∈ V at hx
  have he : a (S.toSpecΓ x) = x :=
    congrArg (fun f : S ⟶ S => f x) (IsIso.hom_inv_id S.toSpecΓ)
  exact he ▸ hx

theorem exists_global_frame_of_coefficient_residue
    {X S Y : Scheme.{u}} [IsAffine S] [IsLocalRing Γ(S, ⊤)]
    (π : X ⟶ S) [IsProper π] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : iSup U = ⊤)
    {D : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
    (φ : D ⟶ SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π L.sheaf U) [QuasiIsoAt φ 0]
    (f : Y ⟶ X) (ρ : Y ⟶ Spec (.of (IsLocalRing.ResidueField Γ(S, ⊤))))
    (H : IsPullback f ρ π
      (AbelianModuli.ReferenceFamily.Affine.CoefficientUnitExactness.coefficientFieldPoint S (IsLocalRing.ResidueField Γ(S, ⊤))))
    [ConnectedSpace Y] [IsReduced Y]
    (he : Nonempty ((L.pullback f).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y))
    (hφ : QuasiIsoAt (CechModelBaseChange.Construction.CechBaseChangeMap.modelMap f π ρ
      (AbelianModuli.ReferenceFamily.Affine.CoefficientUnitExactness.coefficientFieldPoint S (IsLocalRing.ResidueField Γ(S, ⊤)))
      H.w L.sheaf U φ) 0)
    (z : (D.d 0 1).hom.ker)
    (hz : (ModelOneTensor.Construction.CechBaseChangeMap.oneCycle
      (AbelianModuli.ReferenceFamily.Affine.CoefficientUnitExactness.coefficientFieldPoint S (IsLocalRing.ResidueField Γ(S, ⊤))) z).val ≠ 0) :
    Nonempty (L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) := by
  let q := AbelianModuli.ReferenceFamily.Affine.CoefficientUnitExactness.coefficientFieldPoint S (IsLocalRing.ResidueField Γ(S, ⊤))
  have := hφ
  let a := GlobalModel.Construction.GlobalModelSections.equiv π L.sheaf U hU φ z
  let s := (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv L.sheaf).symm a
  have hs : AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f s ≠ 0 := by
    intro h
    have ha := PullbackSectionValue.Construction.PullbackSectionZero.value_zero f s h
    have hv : AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv L.sheaf s = a :=
      (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv L.sheaf).apply_symm_apply a
    rw [hv] at ha
    exact ModelFiberNonzero.Construction.CechBaseChangeMap.global_section_pullback_ne_zero f π ρ q H.w
      L.sheaf U hU φ z hz ha
  let F := Over.mk ρ
  have : IsProper F.hom := MorphismProperty.of_isPullback (P := @IsProper) H inferInstance
  have : ConnectedSpace F.left := inferInstanceAs (ConnectedSpace Y)
  have : IsReduced F.left := inferInstanceAs (IsReduced Y)
  have hi := TrivialBundle.Construction.TrivialBundleFrame.isIso F he.some (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f s) hs
  have hpoint := FieldModelFrameNeighborhood.Construction.SectionTrivialityOpen.mem_of_cartesian_frame π L s f ρ q H
    (IsLocalRing.closedPoint (IsLocalRing.ResidueField Γ(S, ⊤))) hi
  have htop := coefficientResidue_open_eq_top S (SectionTriviality.Construction.SectionTrivialityOpen.baseOpen π L s) hpoint
  have : IsIso s := FieldModelFrameNeighborhood.Construction.SectionTrivialityOpen.isIso_of_baseOpen_eq_top π L s htop
  exact ⟨(asIso s).symm⟩

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.LocalCoefficientFrameNeighborhood.Construction.ModelFrameNeighborhood
