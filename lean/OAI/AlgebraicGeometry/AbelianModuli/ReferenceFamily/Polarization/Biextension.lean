import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.BiextensionFormulaTransport
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarization.Adjoints

/-! # Biextension -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarization.Biextension

noncomputable section

/-! The ample polarization witness on the identity fiber gives its
actual Poincare tensor formula on the original abelian scheme. The
resulting biextension class is the original class defined by lambda. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {g N : ℕ} {δ : Fin g → ℕ}

theorem polarizationBiextensionAt_class {S T : Scheme.{0}}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (f : T ⟶ S) :
    HilbertConstruction.Line.Bundles.LineBundle.classOf (HilbertConstruction.PolarizationData.polarizationBiextensionAt A.dual A.polarization.isogeny.hom f) =
      Adjoints.polarizationBiextensionClass (A.pullback f) := by
  unfold HilbertConstruction.PolarizationData.polarizationBiextensionAt Adjoints.polarizationBiextensionClass
  rw [HilbertConstruction.Pullback.Comparisons.poincareBaseChangeMap_eq_pullbackOverMap]
  exact HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp
    (((Over.pullback f).map A.polarization.isogeny.hom ⊗ₘ 𝟙 (A.abelian.pullback f).scheme).left)
    (A.dual.poincarePullbackOverMap f).left (HilbertConstruction.Line.Bundles.LineBundle.classOf A.dual.poincare)

variable (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)

def polarizationOriginalBiextension : HilbertConstruction.Line.Bundles.LineBundle (A.abelian.scheme ⊗ A.abelian.scheme).left :=
  (HilbertConstruction.PolarizationData.polarizationBiextensionAt A.dual A.polarization.isogeny.hom (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)).pullback
    (A.abelian.pullbackIdIso.inv ⊗ₘ A.abelian.pullbackIdIso.inv).left

theorem polarizationOriginalBiextension_class :
    HilbertConstruction.Line.Bundles.LineBundle.classOf (polarizationOriginalBiextension A) = Adjoints.polarizationBiextensionClass A := by
  change HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.abelian.pullbackIdIso.inv ⊗ₘ A.abelian.pullbackIdIso.inv).left
    (HilbertConstruction.Line.Bundles.LineBundle.classOf (HilbertConstruction.PolarizationData.polarizationBiextensionAt A.dual A.polarization.isogeny.hom (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase))) = _
  rw [polarizationBiextensionAt_class]
  exact Adjoints.polarizationBiextensionClass_iso A (A.pullback (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase))
    (HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackId A).symm

theorem polarizationLineBundle_poincare :
    Nonempty ((((polarizationOriginalBiextension A).tensor
      ((Intrinsic.ChernPairing.polarizationLineBundle A).pullback (fst A.abelian.scheme A.abelian.scheme).left)).tensor
      ((Intrinsic.ChernPairing.polarizationLineBundle A).pullback (snd A.abelian.scheme A.abelian.scheme).left)).sheaf ≅
        ((Intrinsic.ChernPairing.polarizationLineBundle A).pullback (MonObj.mul (X := A.abelian.scheme)).left).sheaf) := by
  obtain ⟨e⟩ := Intrinsic.ChernPairing.polarizationFiberLineBundle_poincare A
  exact ⟨BiextensionFormulaTransport.biextensionFormula_transport A.abelian.scheme (A.abelian.pullback (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)).scheme
    A.abelian.pullbackIdIso.inv (Intrinsic.ChernPairing.polarizationFiberLineBundle A)
    (HilbertConstruction.PolarizationData.polarizationBiextensionAt A.dual A.polarization.isogeny.hom (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) e⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarization.Biextension
