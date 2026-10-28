import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Open.BaseFunctorRepresentation
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.Representations

/-! # Base Functor Representation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.BaseFunctorRepresentation

noncomputable section

/-! A representation over an open base gives a literal local
representation of the original functor, on all tests mapping into that open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Open.BaseFunctorRepresentation
variable {S : Scheme.{0}} (F : (Over S)ᵒᵖ ⥤ Type) (U : S.Opens)

def openRepresentationOfBase (Z : Over U.toScheme)
    (u : F.obj (op ((Over.map U.ι).obj Z)))
    (h : ∀ (T : Over U.toScheme), Function.Bijective
      (fun f : T ⟶ Z => F.map ((Over.map U.ι).map f).op u)) : Representations.OpenRepresentation F U where
  space := (Over.map U.ι).obj Z
  mapsTo z := (Z.hom z).property
  sectionValue := u
  classifies T hT := by
    let e := PELModuli.IntegralModel.Open.BaseFunctorRepresentation.OpenBaseTest.homEquiv U T hT Z
    let q := PELModuli.IntegralModel.Open.BaseFunctorRepresentation.OpenBaseTest.comparison U T hT
    have hb := (ConcreteCategory.bijective_of_isIso (F.map q.hom.op)).comp
      ((h (PELModuli.IntegralModel.Open.BaseFunctorRepresentation.OpenBaseTest.over U T hT)).comp e.bijective)
    convert hb using 1
    funext f
    change F.map f.op u = F.map q.hom.op (F.map ((Over.map U.ι).map (e f)).op u)
    rw [← F.map_comp_apply]
    exact congrArg (fun a : T ⟶ (Over.map U.ι).obj Z => F.map a.op u)
      (PELModuli.IntegralModel.Open.BaseFunctorRepresentation.OpenBaseTest.homEquiv_comparison U T hT Z f).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.BaseFunctorRepresentation
