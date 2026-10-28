import OAI.NumberTheory.PadicHodge.IntegralComparison.PD.FormsBaseQuotientSymbols
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal

/-! # Base Quotient Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PD.BaseQuotientNaturality

noncomputable section

/-!
# IntegralComparison: quotient-base form comparison is natural for actual divided-power algebra maps
-/

open _root_.CategoryTheory

universe u

variable (R S A C : Type u) [CommRing R] [CommRing S] [CommRing A] [CommRing C]
  [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]
  [Algebra S C] [Algebra R C] [IsScalarTower R S C]
  (h : Function.Surjective (algebraMap R S))
  (I : Ideal A) (δI : DividedPowers I) (J : Ideal C) (δJ : DividedPowers J)
  (f : A →ₐ[S] C) (hf : DividedPowers.IsDPMorphism δI δJ f.toRingHom)

theorem naturality (n : ℕ) (ω : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δI n) :
    FormsBaseQuotientSymbols.formsEquiv R S C h J δJ n
      (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap (CommAlgCat.ofHom (f.restrictScalars R)) hf n ω) =
        AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap (CommAlgCat.ofHom f) hf n
          (FormsBaseQuotientSymbols.formsEquiv R S A h I δI n ω) := by
  obtain ⟨a, rfl⟩ := (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relations R A I δI n).mkQ_surjective ω
  obtain ⟨a, rfl⟩ := (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R A n).mkQ_surjective a
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single v a =>
    change FormsBaseQuotientSymbols.formsEquiv R S C h J δJ n
      (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap (CommAlgCat.ofHom (f.restrictScalars R)) hf n (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R A I δI a v)) =
        AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap (CommAlgCat.ofHom f) hf n
          (FormsBaseQuotientSymbols.formsEquiv R S A h I δI n (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R A I δI a v))
    have hR := AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap_symbol (CommAlgCat.ofHom (f.restrictScalars R)) hf n a v
    have hS := AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap_symbol (CommAlgCat.ofHom f) hf n a v
    exact (congrArg (FormsBaseQuotientSymbols.formsEquiv R S C h J δJ n) hR).trans
      ((FormsBaseQuotientSymbols.formsEquiv_symbol R S C h J δJ n (f a) (fun i => f (v i))).trans
        (hS.symm.trans (congrArg (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap (CommAlgCat.ofHom f) hf n)
          (FormsBaseQuotientSymbols.formsEquiv_symbol R S A h I δI n a v).symm)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PD.BaseQuotientNaturality
