import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Fractions
import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.CechTopResidue
import OAI.NumberTheory.PadicHodge.IntegralComparison.SplitExteriorAdjunction

/-! # Top Residue -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.TopResidue

noncomputable section

/-! The ordered top generator for normal equations followed by point
parameters becomes precisely the inverse point-parameter product after
normal top evaluation. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Fractions
variable (R : Type u) [CommRing R] {c m : ℕ}

def basis : Module.Basis (Fin (c + m)) R (Fractions.ambient R (c := c) (m := m)) :=
  SplitExteriorAdjunction.productBasis (Pi.basisFun R (Fin c)) (Pi.basisFun R (Fin m))
    (LinearEquiv.refl R _)

theorem basis_append : (basis R (c := c) (m := m) : _ → _) =
    Fin.append (fun j => (Pi.basisFun R (Fin c) j, 0)) (fun j => (0, Pi.basisFun R (Fin m) j)) := by
  funext j
  refine Fin.addCases (fun k => ?_) (fun k => ?_) j
  · simp [basis, SplitExteriorAdjunction.productBasis, Module.Basis.reindex_apply,
      Module.Basis.map_apply, Module.Basis.prod_apply]
  · simp [basis, SplitExteriorAdjunction.productBasis, Module.Basis.reindex_apply,
      Module.Basis.map_apply, Module.Basis.prod_apply]

def functional : Module.Dual R (⋀[R]^(c + m) (Fractions.ambient R (c := c) (m := m))) :=
  TopExteriorCoordinates.coordinate (basis R)

theorem insertion_top (a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) m) :
    Fractions.insertion R c m a (TopExteriorCoordinates.generator (Pi.basisFun R (Fin c))) =
      TopExteriorCoordinates.generator (basis R) := by
  have ht : Fractions.tuple R (c := c) a = (fun j => (0, Pi.basisFun R (Fin m) j)) := by
    funext j
    exact congrArg (fun k => (0, Pi.basisFun R (Fin m) k))
      (congrFun (Koszul.CechTopResidue.tuple_down a) j)
  change Koszul.OrderedProduct.rightWord R _ c m (Fractions.tuple R a)
    (exteriorPower.map c (LinearMap.inl R (Fractions.normal R (c := c)) (Fractions.parameters R (m := m)))
      (exteriorPower.ιMulti R c (Pi.basisFun R (Fin c)))) = _
  rw [exteriorPower.map_apply_ιMulti, ht, Koszul.OrderedProduct.rightWord_multi]
  change exteriorPower.ιMulti R (c + m)
    (Fin.append (fun j => (Pi.basisFun R (Fin c) j, 0)) (fun j => (0, Pi.basisFun R (Fin m) j))) = _
  rw [← basis_append]
  rfl

variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  (P : Cᵒᵖ ⥤ CommAlgCat.{u} R) (U : ULift.{u} (Fin m) → C)
  (t : Fin m → R) (ht : ∀ i, IsUnit (algebraMap R (P.obj (op (U i))) (t i.down)))

theorem coordinate_top (a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) m) :
    Fractions.coordinate R P U t ht c m a (functional R)
      (TopExteriorCoordinates.generator (Pi.basisFun R (Fin c))) = Fractions.reciprocal R P U t ht a := by
  rw [Fractions.coordinate_apply, insertion_top]
  change Fractions.reciprocal R P U t ht a * algebraMap R _
    (TopExteriorCoordinates.coordinate (basis R) (TopExteriorCoordinates.generator (basis R))) = _
  rw [TopExteriorCoordinates.coordinate_generator, map_one, mul_one]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.TopResidue
