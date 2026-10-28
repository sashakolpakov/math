import OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.AcyclicHomologyData

/-! # Acyclic Homology Naturality -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.AcyclicHomologyNaturality.SemilinearAcyclicHomologyNaturality

noncomputable section

/-! # Semilinear transport of the original acyclic cohomology-to-Ext map -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open _root_.CategoryTheory.Abelian OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.AcyclicHomologyData.SemilinearAcyclicHomologyData

universe u v u' v' z t t'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{z} D]
  (R : Type t) (S : Type t') [CommRing R] [CommRing S] [Linear R C] [Linear S D]
  (σ : R →+* S) (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (hF : ∀ (Y : C) (r : R), F.map (r • 𝟙 Y) = σ r • 𝟙 (F.obj Y))
  (X : C) (T : ShortComplex C) (U : ShortComplex D) (φ : T.map F ⟶ U)
  {A : C} {B : D}
  (a : A ⟶ T.X₁) (ha : a ≫ T.toCycles = 0)
  (b : B ⟶ U.X₁) (hb : b ≫ U.toCycles = 0)
  (β : F.obj A ⟶ B) (hβ : β ≫ b = F.map a ≫ φ.τ₁)
  (hT : (ShortComplex.mk a T.toCycles ha).ShortExact)
  (hU : (ShortComplex.mk b U.toCycles hb).ShortExact)
  [Subsingleton (Ext.{z} X T.X₁ 1)] [Subsingleton (Ext.{z} (F.obj X) U.X₁ 1)]

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor.functor R X 0
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor.functor S (F.obj X) 0
local notation "Q" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.AcyclicHomologyData.SemilinearAcyclicHomologyData.coefficients R S σ
local notation "dT" => OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionHomologyData.data R X T a ha hT
local notation "dU" => OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionHomologyData.data S (F.obj X) U b hb hU

include hβ in
theorem naturality : ShortComplex.homologyMap (AcyclicHomologyData.SemilinearAcyclicHomologyData.sectionMap R S σ F hF X T U φ) ≫
      ((U.map H).mapHomologyIso Q).hom ≫
        (Q).map (NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionHomologyData.homologyIso S (F.obj X) U b hb hU).hom =
    (NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionHomologyData.homologyIso R X T a ha hT).hom ≫
      ExtSections.SemilinearExtSections.map R S σ F hF X β 1 := by
  have ht : ((U.map H).mapHomologyIso Q).hom ≫
      (Q).map (NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionHomologyData.homologyIso S (F.obj X) U b hb hU).hom =
      ((dU).map Q).homologyIso.hom := Mapped.LeftHomologyIso.MappedLeftHomologyIso.homologyIso Q (U.map H) dU
  rw [ht]
  exact (AcyclicHomologyData.SemilinearAcyclicHomologyData.data R S σ F hF X T U φ a ha b hb β hβ hT hU).homologyMap_comm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.AcyclicHomologyNaturality.SemilinearAcyclicHomologyNaturality
