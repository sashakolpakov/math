import OAI.NumberTheory.PadicHodge.IntegralComparison.SiteLifts

/-! # Incoming Slice -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IncomingSlice.IncomingSliceEquivalence

noncomputable section

/-! A fully faithful functor with incoming lifts identifies the actual
over categories, even if it is not essentially surjective globally. -/

open _root_.CategoryTheory

universe u v u' v'
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (F : C ⥤ D) (L : IntegralComparison.SiteLifts.IncomingLifts F) (I : C)

include L in
theorem essSurj : (Over.post (X := I) F).EssSurj := by
  constructor
  intro T
  refine ⟨Over.mk (L.hom T.hom), ⟨?_⟩⟩
  exact Over.isoMk (L.iso T.hom) (L.map_hom T.hom).symm

variable [F.Full] [F.Faithful]

def equivalence : Over I ≌ Over (F.obj I) := by
  letI := essSurj F L I
  letI : (Over.post (X := I) F).IsEquivalence := {}
  exact (Over.post (X := I) F).asEquivalence

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IncomingSlice.IncomingSliceEquivalence
