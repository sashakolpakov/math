import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ScalarRingCycleEquiv
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.CechModelSectionCompatibility
import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Affine Base Point Sections -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AffineBasePointSections.Construction

noncomputable section

/-! The coefficient-ring point of an affine base and its canonical section-lifting condition. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

variable {S : Scheme.{u}} [IsAffine S] {A : Type u} [CommRing A]
variable (a : Γ(S, ⊤) →+* A)

def affineBasePoint : Spec (.of A) ⟶ S := Spec.map (CommRingCat.ofHom a) ≫ S.isoSpec.inv

theorem affineBasePoint_appTop :
    (affineBasePoint a).appTop ≫ (Scheme.ΓSpecIso (.of A)).hom = CommRingCat.ofHom a := by
  have hS : S.isoSpec.inv.appTop ≫ (Scheme.ΓSpecIso Γ(S, ⊤)).hom = 𝟙 Γ(S, ⊤) := by
    rw [← Scheme.toSpecΓ_appTop]
    change S.isoSpec.inv.appTop ≫ S.isoSpec.hom.appTop = 𝟙 Γ(S, ⊤)
    rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id]
    rfl
  rw [affineBasePoint, Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality,
    ← Category.assoc]
  exact (congrArg (fun b : Γ(S, ⊤) ⟶ Γ(S, ⊤) ↦ b ≫ CommRingCat.ofHom a) hS).trans
    (Category.id_comp _)

theorem cochain_cycles_lift_iff_affineBasePoint
    (D : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ) :
    Function.Surjective (CochainBaseChangeCycles.Construction.cochainBaseChangeFirstCycle (affineBasePoint a).appTop.hom D) ↔
      Function.Surjective (CochainBaseChangeCycles.Construction.cochainBaseChangeFirstCycle a D) :=
  ScalarRingCycleEquiv.Construction.cochain_cycles_lift_iff_of_scalarRingIso (affineBasePoint a).appTop.hom a
    (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv
    (fun x ↦ ConcreteCategory.congr_hom (affineBasePoint_appTop a) x) D

theorem affineBasePoint_model_sections_surjective_iff
    {X Y : Scheme.{u}} (f : Y ⟶ X) (π : X ⟶ S) (ρ : Y ⟶ Spec (.of A))
    (h : f ≫ π = ρ ≫ affineBasePoint a) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : iSup U = ⊤)
    {D : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
    (φ : D ⟶ OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U) [QuasiIsoAt φ 0]
    [QuasiIsoAt (OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechModelBaseChange.Construction.CechBaseChangeMap.modelMap f π ρ (affineBasePoint a) h M U φ) 0] :
    Function.Surjective (OpenPullbackSections.Construction.modulePullbackSection f M ⊤) ↔
      Function.Surjective (CochainBaseChangeCycles.Construction.cochainBaseChangeFirstCycle a D) :=
  (CechModelSectionCompatibility.Construction.cechModel_sections_surjective_iff_cycles_lift f π ρ (affineBasePoint a) h M U hU φ).trans
    (cochain_cycles_lift_iff_affineBasePoint a D)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AffineBasePointSections.Construction
