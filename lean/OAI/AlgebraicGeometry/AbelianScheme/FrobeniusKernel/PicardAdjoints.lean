import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Polarization
import OAI.AlgebraicGeometry.PELModuli.CMPoints.DualityPairing

/-! # Picard Adjoints -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardAdjoints.Construction

noncomputable section

/-!
A Poincare adjoint is the canonical Picard pullback map. Hence the actual
source Rosati equation and the CMPoints torsion adjoint condition can be
written with that uniquely determined native dual map.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

namespace NativePicardPullback

variable {S : Scheme.{u}} {g h : ℕ}
variable {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S}
variable (f : A.scheme ⟶ B.scheme) [IsMonHom f]
variable (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)

/-- The Poincare pullback equation determines the native dual morphism. -/
theorem dualMap_eq_of_poincare
    (d : DB.abelian.scheme ⟶ DA.abelian.scheme)
    (hd : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (d ⊗ₘ 𝟙 A.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DA.poincare) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 DB.abelian.scheme ⊗ₘ f).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DB.poincare)) :
    d = PicardPullback.Construction.IntrinsicPicardPullback.dualMap f DA DB := by
  rw [Polarization.Construction.NativePicardPullback.dualMap_eq_e57]
  apply Picard.Homomorphisms.PoincareDetection.Construction.poincareClass_injective DA DB.abelian.scheme
  have h₁ : Picard.Homomorphisms.PoincareDetection.Construction.poincareClass DA d =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op DB.abelian.scheme)
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (DB.abelian.scheme ◁ f).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DB.poincare)) := by
    have hleft : d ⊗ₘ 𝟙 A.scheme = d ▷ A.scheme := by
      simp only [MonoidalCategory.tensorHom_def, whiskerLeft_id, Category.comp_id]
    have hright : 𝟙 DB.abelian.scheme ⊗ₘ f = DB.abelian.scheme ◁ f := by
      simp only [MonoidalCategory.tensorHom_def, id_whiskerRight, Category.id_comp]
    rw [hleft, hright] at hd
    exact congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op DB.abelian.scheme)) hd
  have h₂ := Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback_poincare DA DB f (𝟙 DB.abelian.scheme)
  rw [Category.id_comp, Picard.Homomorphisms.PoincareDetection.Construction.poincareClass_id] at h₂
  have h₃ := Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullback_toRelativePicard_apply f DB.abelian.scheme
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DB.poincare)
  exact h₁.trans (h₂.trans h₃).symm

end NativePicardPullback

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
variable {S : Scheme} {g N : ℕ} {δ : Fin g → ℕ}
variable (PEL : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) PEL.abelian)

/-- Source Rosati conjugation uses the actual canonical dual action. -/
theorem rosati_canonicalDual (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation PEL ρ)
    (a : NumberField.RingOfIntegers E) :
    PEL.polarization.isogeny.hom ≫ PicardPullback.Construction.IntrinsicPicardPullback.dualMap (ρ.map a) PEL.dual PEL.dual =
      ρ.map (NumberField.IsCMField.ringOfIntegersComplexConj E a) ≫ PEL.polarization.isogeny.hom := by
  obtain ⟨d, _, hd, hros⟩ := hρ a
  exact (congrArg (fun z => PEL.polarization.isogeny.hom ≫ z)
    (NativePicardPullback.dualMap_eq_of_poincare (ρ.map a) PEL.dual PEL.dual d hd).symm).trans hros

/-- The Poincare-adjoint predicate of CMPoints identifies the same native
Picard pullback, without any new compatibility premise. -/
theorem l45PoincareAdjoint_eq_dualMap
    (f : PEL.abelian.scheme ⟶ PEL.abelian.scheme) [IsMonHom f]
    (d : PEL.dual.abelian.scheme ⟶ PEL.dual.abelian.scheme)
    (hd : PELModuli.CMPoints.DualityPairing.PoincareAdjoint PEL f d) :
    d = PicardPullback.Construction.IntrinsicPicardPullback.dualMap f PEL.dual PEL.dual :=
  NativePicardPullback.dualMap_eq_of_poincare f PEL.dual PEL.dual d hd

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardAdjoints.Construction
