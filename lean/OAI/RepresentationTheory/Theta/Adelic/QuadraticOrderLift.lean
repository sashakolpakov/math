import OAI.RepresentationTheory.Theta.Adelic.QuadraticIntegralCoefficients

/-! # Quadratic Order Lift -/

namespace OAI.RepresentationTheory.Theta.Adelic.QuadraticOrderLift

noncomputable section

/-! The coefficient order in a quadratic algebra is exactly the
quadratic algebra over the base order, including its integral units. -/

open OAI.RepresentationTheory.Theta.Adelic.QuadraticIntegralCoefficients

variable {R : Type*} [CommRing R] (S : Subring R) (d : R) (hd : d ∈ S)

def orderMap : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic S (⟨d, hd⟩ : S) →+* QuadraticIntegralCoefficients.coefficientOrder S d hd :=
  (Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange S.subtype (⟨d, hd⟩ : S)).codRestrict _ (fun z => ⟨z.re.property, z.im.property⟩)

def orderEquiv : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic S (⟨d, hd⟩ : S) ≃+* QuadraticIntegralCoefficients.coefficientOrder S d hd :=
  RingEquiv.ofBijective (orderMap S d hd) ⟨by
    intro x y h
    have hr := congrArg (fun z : QuadraticIntegralCoefficients.coefficientOrder S d hd => z.val.re) h
    have hi := congrArg (fun z : QuadraticIntegralCoefficients.coefficientOrder S d hd => z.val.im) h
    exact QuadraticAlgebra.ext (Subtype.ext hr) (Subtype.ext hi), by
    intro z
    refine ⟨⟨⟨z.val.re, z.property.1⟩, ⟨z.val.im, z.property.2⟩⟩, ?_⟩
    rfl⟩

def integralElement (z : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic R d) (hz : z ∈ QuadraticIntegralCoefficients.coefficientOrder S d hd) :
    Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic S (⟨d, hd⟩ : S) := (orderEquiv S d hd).symm ⟨z, hz⟩

theorem integralElement_map (z : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic R d) (hz : z ∈ QuadraticIntegralCoefficients.coefficientOrder S d hd) :
    Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange S.subtype (⟨d, hd⟩ : S) (integralElement S d hd z hz) = z :=
  congrArg Subtype.val ((orderEquiv S d hd).apply_symm_apply ⟨z, hz⟩)

def orderUnit (u : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic R d)ˣ)
    (hu : u.val ∈ QuadraticIntegralCoefficients.coefficientOrder S d hd) (hi : u.inv ∈ QuadraticIntegralCoefficients.coefficientOrder S d hd) :
    (QuadraticIntegralCoefficients.coefficientOrder S d hd)ˣ where
  val := ⟨u.val, hu⟩
  inv := ⟨u.inv, hi⟩
  val_inv := Subtype.ext u.val_inv
  inv_val := Subtype.ext u.inv_val

def integralUnit (u : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic R d)ˣ)
    (hu : u.val ∈ QuadraticIntegralCoefficients.coefficientOrder S d hd) (hi : u.inv ∈ QuadraticIntegralCoefficients.coefficientOrder S d hd) :
    (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic S (⟨d, hd⟩ : S))ˣ :=
  Units.map (orderEquiv S d hd).symm.toMonoidHom (orderUnit S d hd u hu hi)

theorem integralUnit_map (u : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic R d)ˣ)
    (hu : u.val ∈ QuadraticIntegralCoefficients.coefficientOrder S d hd) (hi : u.inv ∈ QuadraticIntegralCoefficients.coefficientOrder S d hd) :
    Units.map (Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange S.subtype (⟨d, hd⟩ : S)).toMonoidHom (integralUnit S d hd u hu hi) = u := by
  apply Units.ext
  exact integralElement_map S d hd u.val hu

end

end OAI.RepresentationTheory.Theta.Adelic.QuadraticOrderLift
