import OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamEquivalence

/-! # Relative Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.RelativeIso

noncomputable section

/-!
# IntegralComparison: isomorphisms of original crystalline objects over a relative base
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

universe u

variable {p : ℕ} {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)}
  {U V R : BigCrystallineSite.Object p B J δ f} (ρU : U ⟶ R) (ρV : V ⟶ R)
  (e : U ≅ V) (he : e.hom ≫ ρV = ρU)

def ringEquiv : V.ring ≃+* U.ring where
  toFun := e.hom.ringMap
  invFun := e.inv.ringMap
  left_inv a := congrArg (fun α : V ⟶ V => α.ringMap a) e.inv_hom_id
  right_inv a := congrArg (fun α : U ⟶ U => α.ringMap a) e.hom_inv_id
  map_mul' := e.hom.ringMap.toRingHom.map_mul
  map_add' := e.hom.ringMap.toRingHom.map_add

def algEquiv :
    letI : Algebra R.ring U.ring := ρU.ringMap.toRingHom.toAlgebra
    letI : Algebra R.ring V.ring := ρV.ringMap.toRingHom.toAlgebra
    V.ring ≃ₐ[R.ring] U.ring := by
  letI : Algebra R.ring U.ring := ρU.ringMap.toRingHom.toAlgebra
  letI : Algebra R.ring V.ring := ρV.ringMap.toRingHom.toAlgebra
  exact { ringEquiv e with commutes' a := congrArg (fun α : U ⟶ R => α.ringMap a) he }

def formsEquiv (n : ℕ) :
    letI : Algebra R.ring U.ring := ρU.ringMap.toRingHom.toAlgebra
    letI : Algebra R.ring V.ring := ρV.ringMap.toRingHom.toAlgebra
    AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R.ring V.ring V.ideal V.dividedPowers n ≃ₗ[R.ring]
      AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R.ring U.ring U.ideal U.dividedPowers n := by
  letI : Algebra R.ring U.ring := ρU.ringMap.toRingHom.toAlgebra
  letI : Algebra R.ring V.ring := ρV.ringMap.toRingHom.toAlgebra
  exact AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamEquivalence.PDDeRhamEquivalence.formsEquiv
    (A := CommAlgCat.of R.ring V.ring) (B := CommAlgCat.of R.ring U.ring)
    (algEquiv ρU ρV e he) e.hom.ringMap.isDPMorphism e.inv.ringMap.isDPMorphism n

theorem formsEquiv_symbol (n : ℕ) (a : V.ring) (t : Fin n → V.ring) :
    letI : Algebra R.ring U.ring := ρU.ringMap.toRingHom.toAlgebra
    letI : Algebra R.ring V.ring := ρV.ringMap.toRingHom.toAlgebra
    formsEquiv ρU ρV e he n (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R.ring V.ring V.ideal V.dividedPowers a t) =
      AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R.ring U.ring U.ideal U.dividedPowers
        (e.hom.ringMap a) (fun i => e.hom.ringMap (t i)) := by
  let : Algebra R.ring U.ring := ρU.ringMap.toRingHom.toAlgebra
  let : Algebra R.ring V.ring := ρV.ringMap.toRingHom.toAlgebra
  exact AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap_symbol (A := CommAlgCat.of R.ring V.ring)
    (B := CommAlgCat.of R.ring U.ring) (CommAlgCat.ofHom (algEquiv ρU ρV e he).toAlgHom)
    e.hom.ringMap.isDPMorphism n a t

theorem formsEquiv_differential (n : ℕ) :
    letI : Algebra R.ring U.ring := ρU.ringMap.toRingHom.toAlgebra
    letI : Algebra R.ring V.ring := ρV.ringMap.toRingHom.toAlgebra
    ∀ ω : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R.ring V.ring V.ideal V.dividedPowers n,
    formsEquiv ρU ρV e he (n + 1) (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential R.ring V.ring V.ideal V.dividedPowers n ω) =
      AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential R.ring U.ring U.ideal U.dividedPowers n (formsEquiv ρU ρV e he n ω) := by
  let : Algebra R.ring U.ring := ρU.ringMap.toRingHom.toAlgebra
  let : Algebra R.ring V.ring := ρV.ringMap.toRingHom.toAlgebra
  exact AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamEquivalence.PDDeRhamEquivalence.formsEquiv_differential (A := CommAlgCat.of R.ring V.ring)
    (B := CommAlgCat.of R.ring U.ring) (algEquiv ρU ρV e he)
    e.hom.ringMap.isDPMorphism e.inv.ringMap.isDPMorphism n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.RelativeIso
