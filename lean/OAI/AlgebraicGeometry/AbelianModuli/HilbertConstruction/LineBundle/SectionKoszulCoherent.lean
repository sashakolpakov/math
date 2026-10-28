import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.SectionKoszulComplex
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LeftTensorCoherence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ZeroModuleCoherence

/-! # Section Koszul Coherent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.SectionKoszulCoherent

noncomputable section

/-! Every term of the finite section Koszul complex with coherent coefficients is coherent. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem lineBundleSectionKoszulComplex_coherent {X : Scheme.{u}} (L : Line.Bundles.LineBundle X)
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (ss : List (Line.Bundles.structureModule X ⟶ L.sheaf)) (i : ℤ) :
    ((SectionKoszulComplex.lineBundleSectionKoszulComplex L M ss).X i).IsQuasicoherent ∧
      ((SectionKoszulComplex.lineBundleSectionKoszulComplex L M ss).X i).IsFiniteType := by
  induction ss generalizing i with
  | nil =>
    by_cases hi : i = 0
    · subst i
      simpa only [SectionKoszulComplex.lineBundleSectionKoszulComplex, HomologicalComplex.single_obj_X_self] using
        (show M.IsQuasicoherent ∧ M.IsFiniteType from ⟨inferInstance, inferInstance⟩)
    · exact ZeroModuleCoherence.module_coherent_of_isZero _
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M i hi)
  | cons s ss ih =>
    let C := SectionKoszulComplex.lineBundleSectionKoszulComplex L M ss
    change ((SectionKoszulStep.lineBundleSectionKoszulStep L s C).X i).IsQuasicoherent ∧
      ((SectionKoszulStep.lineBundleSectionKoszulStep L s C).X i).IsFiniteType
    let F := (TensorEquivalence.lineBundleTensorEquivalence L).functor
    have hnext := ih (i + 1)
    have hhere := ih i
    have : (C.X (i + 1)).IsQuasicoherent := hnext.1
    have : (C.X (i + 1)).IsFiniteType := hnext.2
    have : (C.X i).IsQuasicoherent := hhere.1
    have : (C.X i).IsFiniteType := hhere.2
    have : (F.obj (C.X i)).IsQuasicoherent := LeftTensorCoherence.lineBundleTensorLeft_quasicoherent L _
    have : (F.obj (C.X i)).IsFiniteType := LeftTensorCoherence.lineBundleTensorLeft_finiteType L _
    have hq := Coherent.BinaryBiproduct.module_biprod_quasicoherent (C.X (i + 1)) (F.obj (C.X i))
    have := Coherent.BinaryBiproduct.module_biprod_finiteType (C.X (i + 1)) (F.obj (C.X i))
    let e : (SectionKoszulStep.lineBundleSectionKoszulStep L s C).X i ≅ C.X (i + 1) ⊞ F.obj (C.X i) :=
      HomologicalComplex.homotopyCofiber.XIsoBiprod (SectionKoszulStep.lineBundleSectionComplexMap L s C)
        i (i + 1) rfl
    have hsource : ((SectionKoszulStep.lineBundleSectionKoszulStep L s C).X i).IsQuasicoherent :=
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e.symm hq
    exact ⟨hsource, Quasicoherent.RestrictionFiniteType.quasicoherent_finiteType_of_iso e.symm⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.SectionKoszulCoherent
