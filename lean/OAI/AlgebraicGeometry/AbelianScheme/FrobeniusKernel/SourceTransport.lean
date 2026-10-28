import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardAdjoints
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Prescribed
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Isomorphisms

/-! # Source Transport -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SourceTransport.Construction

noncomputable section

/-! Transport the source of a quotient through a full native source
isomorphism. The source polarization comparison and embedded-kernel
condition follow from the original isomorphism and inclusion square. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Isomorphisms

variable {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
variable {A B : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S} (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A B)

theorem levelIso_dual_inv_eq_native :
    e.dual.inv = PicardPullback.Construction.IntrinsicPicardPullback.dualMap e.abelian.hom A.dual B.dual := by
  apply PicardAdjoints.Construction.NativePicardPullback.dualMap_eq_of_poincare
  have hm : (e.dual.inv ⊗ₘ 𝟙 A.abelian.scheme).left ≫
      (e.dual.hom ⊗ₘ e.abelian.hom).left = (𝟙 B.dual.abelian.scheme ⊗ₘ e.abelian.hom).left := by
    rw [← Over.comp_left, tensorHom_comp_tensorHom, e.dual.inv_hom_id, Category.id_comp]
  exact (congrArg (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (e.dual.inv ⊗ₘ 𝟙 A.abelian.scheme).left)
    e.poincare.symm).trans
      ((AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp (e.dual.inv ⊗ₘ 𝟙 A.abelian.scheme).left
        (e.dual.hom ⊗ₘ e.abelian.hom).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf B.dual.poincare)).symm.trans
          (congrArg (fun f => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf B.dual.poincare)) hm))

theorem levelIso_polarization_pullback :
    PolarizationComparison.Construction.polarizationPullbackHom e.abelian.hom A.dual B.dual B.polarization = A.polarization.isogeny.hom := by
  unfold PolarizationComparison.Construction.polarizationPullbackHom
  rw [← levelIso_dual_inv_eq_native e, ← Category.assoc, ← e.polarization,
    Category.assoc, e.dual.hom_inv_id, Category.comp_id]

theorem levelIso_nativeDual_isMonHom : IsMonHom (PicardPullback.Construction.IntrinsicPicardPullback.dualMap e.abelian.hom A.dual B.dual) := by
  rw [← levelIso_dual_inv_eq_native e]
  exact inferInstanceAs (IsMonHom e.dual.inv)

theorem polarizationPullbackHom_composition {g₁ g₂ g₃ : ℕ}
    {A₀ : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g₁ S} {B₀ : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g₂ S} {C₀ : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g₃ S}
    (p : A₀.scheme ⟶ B₀.scheme) [IsMonHom p] (q : B₀.scheme ⟶ C₀.scheme) [IsMonHom q]
    (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A₀) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B₀) (DC : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData C₀)
    {ε : Fin g₃ → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization DC ε) :
    PolarizationComparison.Construction.polarizationPullbackHom (p ≫ q) DA DC pol =
      p ≫ PolarizationComparison.Construction.polarizationPullbackHom q DB DC pol ≫ PicardPullback.Construction.IntrinsicPicardPullback.dualMap p DA DB := by
  unfold PolarizationComparison.Construction.polarizationPullbackHom
  rw [PicardPullback.Construction.IntrinsicPicardPullback.dualMap_comp p DA DB DC q]
  simp only [Category.assoc]

theorem source_power_transport {A₀ B₀ C₀ D₀ : Over S}
    [GrpObj C₀] [GrpObj D₀] (a : A₀ ⟶ B₀) (b : B₀ ⟶ C₀)
    (c : C₀ ⟶ D₀) [IsMonHom c] (z : A₀ ⟶ D₀)
    (hz : a ≫ b ≫ c = z) (m : ℕ) : a ≫ (b ^ m) ≫ c = z ^ m := by
  rw [MonObj.pow_comp, MonObj.comp_pow, hz]

theorem polarizationPullbackHom_sourceIso {h : ℕ} {C : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S}
    (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B.abelian C) (DC : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData C)
    {ε : Fin h → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization DC ε) (m : ℕ)
    (hp : PolarizationComparison.Construction.polarizationPullbackHom f.hom B.dual DC pol = B.polarization.isogeny.hom ^ m) :
    PolarizationComparison.Construction.polarizationPullbackHom (e.abelian.hom ≫ f.hom) A.dual DC pol = A.polarization.isogeny.hom ^ m := by
  have : IsMonHom (PicardPullback.Construction.IntrinsicPicardPullback.dualMap e.abelian.hom A.dual B.dual) :=
    levelIso_nativeDual_isMonHom e
  exact (polarizationPullbackHom_composition e.abelian.hom f.hom A.dual B.dual DC pol).trans
    ((congrArg (fun z => e.abelian.hom ≫ z ≫ PicardPullback.Construction.IntrinsicPicardPullback.dualMap e.abelian.hom A.dual B.dual) hp).trans
      (source_power_transport e.abelian.hom B.polarization.isogeny.hom
        (PicardPullback.Construction.IntrinsicPicardPullback.dualMap e.abelian.hom A.dual B.dual)
        A.polarization.isogeny.hom (levelIso_polarization_pullback e) m))

variable {A A' B H H' : Over S} [GrpObj A] [GrpObj A'] [GrpObj B]
variable (p : A ⟶ B) (i : H ⟶ A) (i' : H' ⟶ A')
variable (eA : A' ≅ A) (eH : H' ≅ H)
variable (he : i' ≫ eA.hom = eH.hom ≫ i)

include he in
omit [GrpObj A] [GrpObj A'] in
theorem prescribedKernel_transport (hp : Prescribed.Construction.PrescribedKernel p i) :
    Prescribed.Construction.PrescribedKernel (eA.hom ≫ p) i' := by
  intro T a
  let e : (T ⟶ H') ≃ (T ⟶ H) := {
    toFun := fun z => z ≫ eH.hom
    invFun := fun z => z ≫ eH.inv
    left_inv := fun z => by simp only [Category.assoc, eH.hom_inv_id, Category.comp_id]
    right_inv := fun z => by simp only [Category.assoc, eH.inv_hom_id, Category.comp_id] }
  have hlift : (∃! z : T ⟶ H', z ≫ i' = a) ↔ ∃! z : T ⟶ H, z ≫ i = a ≫ eA.hom := by
    apply e.existsUnique_congr
    intro z
    have hz : (z ≫ i') ≫ eA.hom = (e z) ≫ i := by
      change (z ≫ i') ≫ eA.hom = (z ≫ eH.hom) ≫ i
      rw [Category.assoc, he, Category.assoc]
    constructor
    · intro ha
      exact hz.symm.trans (congrArg (fun r => r ≫ eA.hom) ha)
    · intro ha
      exact (cancel_mono eA.hom).mp (hz.trans ha)
  simpa only [Category.assoc] using (hp T (a ≫ eA.hom)).trans hlift.symm

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SourceTransport.Construction
