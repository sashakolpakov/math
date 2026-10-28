import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.LocalMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.IncomingMap

/-! # Family Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSection.FamilyCoordinates.Family

noncomputable section

/-! Equal families of opens give the same canonical section map
whether the family is presented as an order homomorphism or a functor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w
variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of B)) [IsSeparated f] (n : ℕ)
  {C : Type v} [Preorder C] {D : Type w} [Preorder D]
  (r : C ⥤ D) (F : C →o Y.Opens) (G : D →o Y.Opens)
  (h : F = BoundedOpen.IncomingMap.reindexedOpens G r)
  (h' : F.toFunctor.op = r.op ⋙ G.toFunctor.op)
  (K : CochainComplex (BoundedCrystalline.Site.ModuleSheaf (p := p) (J := J) (δ := δ) f n) ℕ)

omit [Fact (Nat.Prime p)] [IsSeparated f] in
theorem comparison :
    ((NatIso.mapHomologicalComplex
      (BoundedFrame.LocalMap.sectionsIso f n F.toFunctor.op (r.op ⋙ G.toFunctor.op) h')
      (.up ℕ)).app K).hom =
    ((NatIso.mapHomologicalComplex
      (BoundedOpen.IncomingMap.familyIso f n F (BoundedOpen.IncomingMap.reindexedOpens G r) h)
      (.up ℕ)).app K).hom := by
  subst F
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSection.FamilyCoordinates.Family
