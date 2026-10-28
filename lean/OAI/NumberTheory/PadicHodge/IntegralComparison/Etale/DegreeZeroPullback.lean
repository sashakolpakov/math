import OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaleDegreeZero
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.Frobenius

/-! # Degree Zero Pullback -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.DegreeZeroPullback

noncomputable section

/-! Original degree-zero pro-étale pullback is precomposition on actual continuous sections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.AlgebraicGeometry Opposite

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.Cohomology OAI.NumberTheory.PadicHodge.IntegralComparison.ProEtale OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.Frobenius OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaleDegreeZero
open OAI.NumberTheory.PadicHodge.PeriodInvariants.ConstantSheafCoherence OAI.NumberTheory.PadicHodge.PeriodInvariants.DegreeZeroSections

variable (ℓ : ℕ) [Fact ℓ.Prime] {X Y : Scheme.{u}}

theorem sections_mk₀ (f : Cohomology.constantUnitSheaf ℓ X ⟶ Cohomology.rationalCoefficientSheaf ℓ X) :
    PeriodInvariants.EtaleDegreeZero.sectionsEquiv ℓ X (Ext.mk₀ f) =
      (f.hom.app (op (Scheme.ProEt.mk (𝟙 X))))
        ((PeriodInvariants.ConstantSheafCoherence.constantGenerator (Scheme.ProEt.topology X)
          (ModuleCat.of (Cohomology.Coeff.{u} ℓ) (Cohomology.Coeff.{u} ℓ))).app
            (op (Scheme.ProEt.mk (𝟙 X))) (1 : Cohomology.Coeff.{u} ℓ)) := by
  dsimp only [Cohomology.constantUnitSheaf] at f
  change PeriodInvariants.DegreeZeroSections.homSectionsLinearEquiv (Scheme.ProEt.topology X) (Cohomology.Coeff.{u} ℓ)
    (PeriodInvariants.EtaleDegreeZero.identityTerminal X) _ (Ext.linearEquiv₀ (Ext.mk₀ f)) = _
  rw [show Ext.linearEquiv₀ (R := Cohomology.Coeff.{u} ℓ) (Ext.mk₀ f) = f from
    (Ext.linearEquiv₀ (R := Cohomology.Coeff.{u} ℓ)).apply_symm_apply f]
  change PeriodInvariants.DegreeZeroSections.homSectionsEquiv _ _ _ _ f = _
  rw [PeriodInvariants.DegreeZeroSections.homSectionsEquiv_apply, Adjunction.homEquiv_unit, PeriodInvariants.ConstantSheafCoherence.constantAdj_unit_app]
  rfl

theorem transport_mk₀ (e : X ≅ Y)
    (f : Cohomology.constantUnitSheaf ℓ X ⟶ Cohomology.rationalCoefficientSheaf ℓ X) :
    Frobenius.cohomologyTransport ℓ e 0 (Ext.mk₀ f) =
      Ext.mk₀ ((Frobenius.constantUnitTransport ℓ e).inv ≫
        (ProEtale.proEtaleSheafCongr (ModuleCat.{u + 1} (Cohomology.Coeff.{u} ℓ)) e).functor.map f ≫
          (Frobenius.coefficientSheafTransport ℓ e).hom) := by
  change ((Ext.mk₀ _).comp ((Ext.mk₀ f).mapExactFunctor _) (Nat.zero_add 0)).comp
    (Ext.mk₀ _) (Nat.add_zero 0) = _
  rw [Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀, Category.assoc]

theorem inverse_generator (e : X ≅ Y) :
    PeriodInvariants.ConstantSheafCoherence.constantGenerator (Scheme.ProEt.topology Y) (ModuleCat.of (Cohomology.Coeff.{u} ℓ) (Cohomology.Coeff.{u} ℓ)) ≫
        (Frobenius.constantUnitTransport ℓ e).inv.hom =
      PeriodInvariants.ConstantSheafCoherence.transportedConstantGenerator (ModuleCat.{u + 1} (Cohomology.Coeff.{u} ℓ)) e
        (ModuleCat.of (Cohomology.Coeff.{u} ℓ) (Cohomology.Coeff.{u} ℓ)) := by
  have h := PeriodInvariants.ConstantSheafCoherence.constantTransport_generators (ModuleCat.{u + 1} (Cohomology.Coeff.{u} ℓ)) e
    (ModuleCat.of (Cohomology.Coeff.{u} ℓ) (Cohomology.Coeff.{u} ℓ))
  have hi : (Frobenius.constantUnitTransport ℓ e).hom.hom ≫ (Frobenius.constantUnitTransport ℓ e).inv.hom = 𝟙 _ :=
    ((sheafToPresheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} (Cohomology.Coeff.{u} ℓ))).mapIso
      (Frobenius.constantUnitTransport ℓ e)).hom_inv_id
  change _ ≫ (Frobenius.constantUnitTransport ℓ e).hom.hom = _ at h
  dsimp only [Cohomology.constantUnitSheaf, Frobenius.constantUnitTransport] at *
  rw [← h, Category.assoc, hi, Category.comp_id]

theorem transport (e : X ≅ Y) (z : Cohomology.RationalEllAdicCohomology ℓ X 0) :
    PeriodInvariants.EtaleDegreeZero.sectionsEquiv ℓ Y (Frobenius.cohomologyTransport ℓ e 0 z) =
      (PeriodInvariants.EtaleDegreeZero.sectionsEquiv ℓ X z).comp e.inv.base.hom := by
  obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective (Cohomology.constantUnitSheaf ℓ X)
    (Cohomology.rationalCoefficientSheaf ℓ X)).surjective z
  rw [transport_mk₀, sections_mk₀, sections_mk₀]
  let T := Scheme.ProEt.mk (𝟙 Y)
  let U := (ProEtale.proEtaleCongr e).inverse.obj T
  let g := (PeriodInvariants.EtaleDegreeZero.identityTerminal X).from U
  have hg := congrArg (fun α => α.app (op T)) (inverse_generator ℓ e)
  have hn := f.hom.naturality g.op
  have hc := PeriodInvariants.ConstantSheafCoherence.constantGenerator_naturality (Scheme.ProEt.topology X)
    (ModuleCat.of (Cohomology.Coeff.{u} ℓ) (Cohomology.Coeff.{u} ℓ)) g.op
  change (PeriodInvariants.ConstantSheafCoherence.constantGenerator (Scheme.ProEt.topology X)
    (ModuleCat.of (Cohomology.Coeff.{u} ℓ) (Cohomology.Coeff.{u} ℓ))).app (op (Scheme.ProEt.mk (𝟙 X))) ≫
      (Cohomology.constantUnitSheaf ℓ X).obj.map g.op =
        (PeriodInvariants.ConstantSheafCoherence.constantGenerator (Scheme.ProEt.topology X)
          (ModuleCat.of (Cohomology.Coeff.{u} ℓ) (Cohomology.Coeff.{u} ℓ))).app (op U) at hc
  have hs : (PeriodInvariants.ConstantSheafCoherence.constantGenerator (Scheme.ProEt.topology X)
      (ModuleCat.of (Cohomology.Coeff.{u} ℓ) (Cohomology.Coeff.{u} ℓ))).app (op U) ≫ f.hom.app (op U) =
    (PeriodInvariants.ConstantSheafCoherence.constantGenerator (Scheme.ProEt.topology X)
      (ModuleCat.of (Cohomology.Coeff.{u} ℓ) (Cohomology.Coeff.{u} ℓ))).app (op (Scheme.ProEt.mk (𝟙 X))) ≫
        f.hom.app (op (Scheme.ProEt.mk (𝟙 X))) ≫
          (Cohomology.rationalCoefficientSheaf ℓ X).obj.map g.op := by
    exact (congrArg (fun h => h ≫ f.hom.app (op U)) hc).symm.trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun h => (PeriodInvariants.ConstantSheafCoherence.constantGenerator (Scheme.ProEt.topology X)
          (ModuleCat.of (Cohomology.Coeff.{u} ℓ) (Cohomology.Coeff.{u} ℓ))).app
            (op (Scheme.ProEt.mk (𝟙 X))) ≫ h) hn))
  have hv := congrArg (fun h => h (1 : Cohomology.Coeff.{u} ℓ)) hs
  have hgv := congrArg (fun h => h (1 : Cohomology.Coeff.{u} ℓ)) hg
  change ((Frobenius.constantUnitTransport ℓ e).inv.hom.app (op T))
      ((PeriodInvariants.ConstantSheafCoherence.constantGenerator (Scheme.ProEt.topology Y)
        (ModuleCat.of (Cohomology.Coeff.{u} ℓ) (Cohomology.Coeff.{u} ℓ))).app (op T) (1 : Cohomology.Coeff.{u} ℓ)) =
    (PeriodInvariants.ConstantSheafCoherence.constantGenerator (Scheme.ProEt.topology X)
      (ModuleCat.of (Cohomology.Coeff.{u} ℓ) (Cohomology.Coeff.{u} ℓ))).app (op U) (1 : Cohomology.Coeff.{u} ℓ) at hgv
  change (f.hom.app (op U))
    (((Frobenius.constantUnitTransport ℓ e).inv.hom.app (op T))
      ((PeriodInvariants.ConstantSheafCoherence.constantGenerator (Scheme.ProEt.topology Y)
        (ModuleCat.of (Cohomology.Coeff.{u} ℓ) (Cohomology.Coeff.{u} ℓ))).app (op T) (1 : Cohomology.Coeff.{u} ℓ))) = _
  exact (congrArg (f.hom.app (op U)) hgv).trans hv

theorem pullback (e : X ≅ Y) (z : Cohomology.RationalEllAdicCohomology ℓ Y 0) :
    PeriodInvariants.EtaleDegreeZero.sectionsEquiv ℓ X (Frobenius.cohomologyPullback ℓ e 0 z) =
      (PeriodInvariants.EtaleDegreeZero.sectionsEquiv ℓ Y z).comp e.hom.base.hom :=
  transport ℓ e.symm z

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.DegreeZeroPullback
