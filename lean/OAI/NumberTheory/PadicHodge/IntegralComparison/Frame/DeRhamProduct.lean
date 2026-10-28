import OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.FrameComplexFunctor
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.Product
import OAI.NumberTheory.PadicHodge.IntegralComparison.PD.DeRhamProductNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.PD.DeRhamLeibniz
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cochain.CohomologyCup

/-! # De Rham Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Frame.DeRhamProduct

noncomputable section

/-! The actual contravariant frame PD complexes carry their native
wedge products and graded differential rule. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

section

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite
universe u
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B))

local instance objectAlgebra (U : BigCrystallineSite.Object p B J δ f) : Algebra B U.ring := U.base.toAlgebra

local notation "P" => OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.FrameComplexFunctor.CrystallineFrameComplexFunctor.functor f

theorem natural (a b : ℕ) {U V : (BigCrystallineSite.Object p B J δ f)ᵒᵖ} (α : U ⟶ V)
    (x : ((P).obj U).X a) (y : ((P).obj U).X b) :
    ((P).map α).f (a+b) (RelativeFrame.Product.framePairing U.unop a b x y) =
      RelativeFrame.Product.framePairing V.unop a b
        (((P).map α).f a x) (((P).map α).f b y) :=
  PD.DeRhamProductNaturality.Wedge.formMap_wedge
    (CommAlgCat.ofHom (Crystalline.DeRham.ambientMap f α.unop))
    (Crystalline.DeRham.ambientMap_isDPMorphism f α.unop) a b x y

theorem degreeCast (U : (BigCrystallineSite.Object p B J δ f)ᵒᵖ) {a b : ℕ} (h : a=b)
    (x : ((P).obj U).X a) :
    Cochain.CohomologyCup.degreeCast ((P).obj U) h x =
      PD.DeRhamLeibniz.Wedge.degreeCast B U.unop.ring U.unop.ideal U.unop.dividedPowers h x := by
  subst b
  rfl

end

namespace PDWedge

universe u
variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  (I : Ideal A) (δ : DividedPowers I)

private theorem cochainDegreeCast {a b : ℕ} (h : a=b)
    (x : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δ a) :
    Cochain.CohomologyCup.degreeCast (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.complex R A I δ) h x =
      PD.DeRhamLeibniz.Wedge.degreeCast R A I δ h x := by
  subst b
  rfl

theorem cochain_differential (a b : ℕ)
    (x : (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.complex R A I δ).X a) (y : (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.complex R A I δ).X b) :
    (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.complex R A I δ).d (a+b) (a+b+1) (PD.DeRhamWedge.wedge R A I δ a b x y) =
      Cochain.CohomologyCup.cupInto (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.complex R A I δ)
        (fun i j => (PD.DeRhamWedge.wedge R A I δ i j).restrictScalars₁₂ R R)
        (a+1) b (a+b+1) (by omega) ((AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.complex R A I δ).d a (a+1) x) y +
      (-1 : ℤ)^a • Cochain.CohomologyCup.cupInto (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.complex R A I δ)
        (fun i j => (PD.DeRhamWedge.wedge R A I δ i j).restrictScalars₁₂ R R)
        a (b+1) (a+b+1) (by omega) x ((AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.complex R A I δ).d b (b+1) y) := by
  change _ = Cochain.CohomologyCup.degreeCast (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.complex R A I δ) (by omega)
    (PD.DeRhamWedge.wedge R A I δ (a+1) b ((AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.complex R A I δ).d a (a+1) x) y) +
    (-1 : ℤ)^a • Cochain.CohomologyCup.degreeCast (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.complex R A I δ) (by omega)
      (PD.DeRhamWedge.wedge R A I δ a (b+1) x ((AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.complex R A I δ).d b (b+1) y))
  rw [cochainDegreeCast, cochainDegreeCast]
  dsimp only [AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.complex]
  rw [CochainComplex.of_d, CochainComplex.of_d, CochainComplex.of_d]
  exact PD.DeRhamLeibniz.Wedge.differential_wedge R A I δ a b x y

end PDWedge

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite
universe u
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B))
local notation "P" => OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.FrameComplexFunctor.CrystallineFrameComplexFunctor.functor f

theorem differential (a b : ℕ) (U : (BigCrystallineSite.Object p B J δ f)ᵒᵖ)
    (x : ((P).obj U).X a) (y : ((P).obj U).X b) :
    ((P).obj U).d (a+b) (a+b+1) (RelativeFrame.Product.framePairing U.unop a b x y) =
      Cochain.CohomologyCup.cupInto ((P).obj U)
        (RelativeFrame.Product.framePairing U.unop) (a+1) b (a+b+1) (by omega)
        (((P).obj U).d a (a+1) x) y +
      (-1 : ℤ)^a • Cochain.CohomologyCup.cupInto ((P).obj U)
        (RelativeFrame.Product.framePairing U.unop) a (b+1) (a+b+1) (by omega)
        x (((P).obj U).d b (b+1) y) := by
  let : Algebra B U.unop.ring := U.unop.base.toAlgebra
  exact PDWedge.cochain_differential B U.unop.ring U.unop.ideal
    U.unop.dividedPowers a b x y

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Frame.DeRhamProduct
