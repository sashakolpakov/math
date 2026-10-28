import OAI.NumberTheory.PadicHodge.IntegralComparison.PD.DeRhamWedge
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntegralDeRham.SemilinearProduct
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamSemilinearMap

/-! # De Rham Product Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PD.DeRhamProductNaturality.Wedge

noncomputable section

/-! The original divided-power pullbacks, including change of base ring,
preserve the product induced by concatenation of differential symbols. -/

open _root_.CategoryTheory

universe u

theorem formMap_wedge {R : Type u} [CommRing R] {A B : CommAlgCat.{u} R}
    {I : Ideal A} {J : Ideal B} {δI : DividedPowers I} {δJ : DividedPowers J}
    (f : A ⟶ B) (hf : DividedPowers.IsDPMorphism δI δJ f.hom.toRingHom)
    (p q : ℕ) (x : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δI p) (y : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δI q) :
    AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap f hf (p + q) (DeRhamWedge.wedge R A I δI p q x y) =
      DeRhamWedge.wedge R B J δJ p q (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap f hf p x)
        (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap f hf q y) := by
  obtain ⟨x, rfl⟩ := (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relations R A I δI p).mkQ_surjective x
  obtain ⟨y, rfl⟩ := (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relations R A I δI q).mkQ_surjective y
  rw [DeRhamWedge.quotient_wedge, AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap_mk,
    AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap_mk, AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap_mk, DeRhamWedge.quotient_wedge,
    IntegralDeRham.WedgeNaturality.formMap_wedge]

theorem semilinearMap_wedge
    (R S A B : Type u) [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra S B] (σ : R →+* S) (f : A →+* B)
    (h : ∀ r, f (algebraMap R A r) = algebraMap S B (σ r))
    (I : Ideal A) (δI : DividedPowers I) (J : Ideal B) (δJ : DividedPowers J)
    (hf : DividedPowers.IsDPMorphism δI δJ f)
    (p q : ℕ) (x : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δI p) (y : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δI q) :
    AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamSemilinearMap.PDDeRhamSemilinearMap.formMap R S A B σ f h I δI J δJ hf (p + q)
        (DeRhamWedge.wedge R A I δI p q x y) =
      DeRhamWedge.wedge S B J δJ p q (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamSemilinearMap.PDDeRhamSemilinearMap.formMap R S A B σ f h I δI J δJ hf p x)
        (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamSemilinearMap.PDDeRhamSemilinearMap.formMap R S A B σ f h I δI J δJ hf q y) := by
  obtain ⟨x, rfl⟩ := (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relations R A I δI p).mkQ_surjective x
  obtain ⟨y, rfl⟩ := (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relations R A I δI q).mkQ_surjective y
  rw [DeRhamWedge.quotient_wedge, AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamSemilinearMap.PDDeRhamSemilinearMap.formMap_mk,
    AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamSemilinearMap.PDDeRhamSemilinearMap.formMap_mk, AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamSemilinearMap.PDDeRhamSemilinearMap.formMap_mk, DeRhamWedge.quotient_wedge,
    IntegralDeRham.SemilinearProduct.Wedge.semilinearMap_wedge]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PD.DeRhamProductNaturality.Wedge
