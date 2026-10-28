import OAI.AlgebraicGeometry.PELModuli.CMPoints.CountableLevels
import OAI.ArithmeticGeometry.Descent.CMVariety.CanonicalDualComparisons
import OAI.ArithmeticGeometry.Descent.CMVariety.CountablePolarizationMaps

/-! # Enhancement Transport Codes -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.EnhancementTransportCodes

noncomputable section

/-! Transporting the actual level and designated endomorphisms to one
fixed abelian scheme gives a countable code. Equal codes give the full
unpolarized enhanced comparison, including canonical Poincare duality. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj Classical

def EnhancementTransportCode {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase) (N r : ℕ) :=
  A.FullLevel N × (Fin r → {f : A.scheme ⟶ A.scheme // IsMonHom f})

theorem enhancementTransportCode_countable {g N r : ℕ} [NeZero N]
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase) (level : A.FullLevel N)
    (P : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation A) : Countable (EnhancementTransportCode A N r) := by
  let : Finite (A.FullLevel N) := CountableLevels.finite_full_levels A level
  let : Countable {f : A.scheme ⟶ A.scheme // IsMonHom f} := ArithmeticGeometry.Descent.CMVariety.CountablePolarizationMaps.Abelian.presented_endomorphisms_countable A P
  exact inferInstanceAs (Countable (_ × _))

def enhancementTransportCode {g N r : ℕ} {δ : Fin g → ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase) (B : ArithmeticGeometry.Descent.CMVariety.ModuliObjects.Abelian.EnhancedAbelianData g δ N r Foundations.Scheme.ProjectiveSpace.complexBase)
    (e : A.scheme ≅ B.polarized.abelian.scheme) [IsMonHom e.hom] :
    EnhancementTransportCode A N r := by
  let : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  exact ⟨B.polarized.level.transport e.symm,
    fun i => ⟨e.hom ≫ B.endomorphism i ≫ e.inv, inferInstance⟩⟩

def unpolarizedComparisonOfTransportCodeEq {g N r : ℕ} {δ : Fin g → ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase) (B C : ArithmeticGeometry.Descent.CMVariety.ModuliObjects.Abelian.EnhancedAbelianData g δ N r Foundations.Scheme.ProjectiveSpace.complexBase)
    (e : A.scheme ≅ B.polarized.abelian.scheme) [IsMonHom e.hom]
    (f : A.scheme ≅ C.polarized.abelian.scheme) [IsMonHom f.hom]
    (h : enhancementTransportCode A B e = enhancementTransportCode A C f) :
    ArithmeticGeometry.Descent.CMVariety.UnpolarizedComparisons.Abelian.UnpolarizedEnhancedIso B C := by
  let q := e.symm ≪≫ f
  let : IsMonHom q.hom := inferInstanceAs (IsMonHom (e.inv ≫ f.hom))
  apply ArithmeticGeometry.Descent.CMVariety.CanonicalDualComparisons.Abelian.unpolarizedEnhancedIsoOfGroupLevel q
  · intro i
    have hc := congrArg (fun c : EnhancementTransportCode A N r => (c.2 i).val) h
    change e.hom ≫ B.endomorphism i ≫ e.inv = f.hom ≫ C.endomorphism i ≫ f.inv at hc
    change B.endomorphism i ≫ (e.inv ≫ f.hom) = (e.inv ≫ f.hom) ≫ C.endomorphism i
    apply (cancel_epi e.hom).mp
    apply (cancel_mono f.inv).mp
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id] using hc
  · intro T c
    have hl := congrArg (fun a : EnhancementTransportCode A N r =>
      (a.1.hom.app (.op T) c).val) h
    change (B.polarized.level.hom.app (.op T) c).val ≫ e.inv =
      (C.polarized.level.hom.app (.op T) c).val ≫ f.inv at hl
    change (B.polarized.level.hom.app (.op T) c).val ≫ (e.inv ≫ f.hom) = _
    apply (cancel_mono f.inv).mp
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hl

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.EnhancementTransportCodes
