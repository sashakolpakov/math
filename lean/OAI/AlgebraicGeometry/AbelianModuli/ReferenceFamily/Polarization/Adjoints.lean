import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData

/-! # Adjoints -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The native Rosati equation implies the adjoint identity on the
actual polarization biextension line-bundle class. This is the geometric
identity to which the rational Chern-class pairing will be applied. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {S : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}

def Polarization.Adjoints.polarizationBiextensionClass (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S) :
    HilbertConstruction.Line.Bundles.LineBundle.IsoClass (A.abelian.scheme ⊗ A.abelian.scheme).left :=
  HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.polarization.isogeny.hom ⊗ₘ 𝟙 A.abelian.scheme).left
    (HilbertConstruction.Line.Bundles.LineBundle.classOf A.dual.poincare)

theorem Polarization.Adjoints.polarizationBiextensionClass_iso
    (A B : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (e : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A B) :
    HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (e.abelian.hom ⊗ₘ e.abelian.hom).left
      (Polarization.Adjoints.polarizationBiextensionClass B) = Polarization.Adjoints.polarizationBiextensionClass A := by
  have h : (e.abelian.hom ⊗ₘ e.abelian.hom) ≫
      (B.polarization.isogeny.hom ⊗ₘ 𝟙 B.abelian.scheme) =
        (A.polarization.isogeny.hom ⊗ₘ 𝟙 A.abelian.scheme) ≫
          (e.dual.hom ⊗ₘ e.abelian.hom) := by
    simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
    exact congrArg (fun f => f ⊗ₘ e.abelian.hom) e.polarization.symm
  unfold Polarization.Adjoints.polarizationBiextensionClass
  rw [← HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]
  change HilbertConstruction.Line.Bundles.LineBundle.pullbackClass
    (((e.abelian.hom ⊗ₘ e.abelian.hom) ≫
      (B.polarization.isogeny.hom ⊗ₘ 𝟙 B.abelian.scheme)).left) _ = _
  rw [h, Over.comp_left, HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, e.poincare]

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem ActionData.RosatiConjugation.biextension_adjoint
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (hρ : ActionData.RosatiConjugation A ρ) (a : NumberField.RingOfIntegers E) :
    HilbertConstruction.Line.Bundles.LineBundle.pullbackClass
        (ρ.map (NumberField.IsCMField.ringOfIntegersComplexConj E a) ⊗ₘ 𝟙 A.abelian.scheme).left
          (Polarization.Adjoints.polarizationBiextensionClass A) =
      HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 A.abelian.scheme ⊗ₘ ρ.map a).left
        (Polarization.Adjoints.polarizationBiextensionClass A) := by
  obtain ⟨u, _hu, hp, ha⟩ := hρ a
  let l := A.polarization.isogeny.hom
  let c := NumberField.IsCMField.ringOfIntegersComplexConj E a
  have hleft : (ρ.map c ⊗ₘ 𝟙 A.abelian.scheme) ≫ (l ⊗ₘ 𝟙 A.abelian.scheme) =
      (l ⊗ₘ 𝟙 A.abelian.scheme) ≫ (u ⊗ₘ 𝟙 A.abelian.scheme) := by
    simp only [tensorHom_comp_tensorHom, Category.id_comp]
    exact congrArg (fun f => f ⊗ₘ 𝟙 A.abelian.scheme) ha.symm
  have hright : (l ⊗ₘ 𝟙 A.abelian.scheme) ≫ (𝟙 A.dual.abelian.scheme ⊗ₘ ρ.map a) =
      (𝟙 A.abelian.scheme ⊗ₘ ρ.map a) ≫ (l ⊗ₘ 𝟙 A.abelian.scheme) := by
    simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
  unfold Polarization.Adjoints.polarizationBiextensionClass
  rw [← HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]
  change HilbertConstruction.Line.Bundles.LineBundle.pullbackClass
    (((ρ.map c ⊗ₘ 𝟙 A.abelian.scheme) ≫ (l ⊗ₘ 𝟙 A.abelian.scheme)).left) _ = _
  rw [hleft]
  rw [Over.comp_left, HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, hp,
    ← HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]
  change HilbertConstruction.Line.Bundles.LineBundle.pullbackClass
    (((l ⊗ₘ 𝟙 A.abelian.scheme) ≫ (𝟙 A.dual.abelian.scheme ⊗ₘ ρ.map a)).left) _ = _
  rw [hright, Over.comp_left, HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
