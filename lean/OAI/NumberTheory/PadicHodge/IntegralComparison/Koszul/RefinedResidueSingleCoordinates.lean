import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.RefinedResidueClass
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechSingleTopCoordinates

/-! # Refined Residue Single Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.RefinedResidueSingleCoordinates

noncomputable section

/-! The actual refined point residue has the original single-complex
coordinate. Its scalar is the original point functional and its sole
sign is the coefficient-degree/Čech-degree interchange sign. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Fractions OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Components
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  (R : Type u) [CommRing R] (P : Cᵒᵖ ⥤ CommAlgCat.{u} R)
  {c m : ℕ} (U : ULift.{u} (Fin m) → C) (s : Fin c → R) (t : Fin m → R)
  (ht : ∀ i, IsUnit (algebraMap R (P.obj (op (U i))) (t i.down)))
  (N : Cᵒᵖ ⥤ ModuleCat.{u} R) (α : KoszulPartial.Fractions.modules R P ⟶ N)
  (k : Type u) [CommRing k] [Algebra k R]

private theorem cardinal : Fintype.card (ULift.{u} (Fin m)) = m := by simp

def scalarValue (a : k) : N.obj (op (AugmentedOrdered.CechCoordinates.topObject U m (cardinal (m := m)))) :=
  α.app (op (AugmentedOrdered.CechCoordinates.topObject U m (cardinal (m := m))))
    ((show P.obj (op (AugmentedOrdered.CechCoordinates.topObject U m (cardinal (m := m)))) from
      KoszulPartial.Fractions.reciprocal R P U t ht (AugmentedOrdered.CechCoordinates.topIndex m (cardinal (m := m)))) *
      algebraMap R (P.obj (op (AugmentedOrdered.CechCoordinates.topObject U m (cardinal (m := m))))) (algebraMap k R a))

theorem scalarValue_smul (a : k) :
    scalarValue R P U t ht N α k a = algebraMap k R a •
      α.app (op (AugmentedOrdered.CechCoordinates.topObject U m (cardinal (m := m))))
        (KoszulPartial.Fractions.reciprocal R P U t ht (AugmentedOrdered.CechCoordinates.topIndex m (cardinal (m := m)))) := by
  change α.app _ (_ * algebraMap R _ (algebraMap k R a)) = _
  rw [mul_comm]
  let o := op (AugmentedOrdered.CechCoordinates.topObject U m (cardinal (m := m)))
  let v : P.obj o := KoszulPartial.Fractions.reciprocal R P U t ht (AugmentedOrdered.CechCoordinates.topIndex m (cardinal (m := m)))
  have hs : algebraMap R (P.obj o) (algebraMap k R a) * v = (algebraMap k R a) • v :=
    (Algebra.smul_def (algebraMap k R a) v).symm
  change (α.app o).hom (algebraMap R (P.obj o) (algebraMap k R a) * v) = _
  rw [hs]
  exact (α.app o).hom.map_smul (algebraMap k R a) v

variable {L : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} R) ℕ}
  (eP : HomotopyEquiv L (KoszulPartial.Components.coefficient R P (Fin.append s t)))
  (hP : Function.Bijective (algebraMap R (P.obj (op (⊤_ C)))))
  (d : ℕ) (hL : ∀ q, q ≠ d → L.ExactAt q)
  (hzero : ∀ p q, 0 < q → ∀ a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) q,
    IsZero ((((single (Cᵒᵖ ⥤ ModuleCat R) (.up ℕ) d).obj (L.homology d)).X p).obj
      (op ((AugmentedOrdered.Cech.formal U q).obj a))))
  (e₀ : (R ⧸ OrientedTopCohomology.ideal R (Fin.append s t)) ≃ₐ[k] k)

theorem value (y : (Supported.CechHomotopyEquivalence.functor U (c+m)).obj L) :
    CoefficientResidueClass.residueValue R P U t ht N α
      (RefinedScalarFraction.functional R P U s t eP k hP d hL hzero e₀ y) =
    AugmentedOrdered.CechSingleTopCoordinates.singleValue U N m (cardinal (m := m)) c
      (scalarValue R P U t ht N α k
        (KoszulPoint.ScalarCoordinates.scalar k R P hP U s t eP d hL hzero e₀ y)) := by
  dsimp only [CoefficientResidueClass.residueValue,
    AugmentedOrdered.CechSingleTopCoordinates.singleValue, scalarValue]
  rw [RefinedScalarFraction.evaluation]

theorem coordinates (y : (Supported.CechHomotopyEquivalence.functor U (c+m)).obj L) :
    (Functor.SingleTotal.homologyIso (AugmentedOrdered.CechFunctor.functor U) N c m).hom
      ((eqToHom (congrArg
        (fun j => ((AugmentedOrdered.CechFunctor.bicomplex U (CoefficientResidueClass.residueTarget R (c := c) N)).total
          (.up ℕ)).homology j) (Nat.add_comm c m)))
        (RefinedResidueClass.residueClass R P U s t ht eP k hP d hL hzero e₀ N α y)) =
      ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) c m •
        AugmentedOrdered.CechTopClass.topClass U N m (cardinal (m := m)) (scalarValue R P U t ht N α k
          (KoszulPoint.ScalarCoordinates.scalar k R P hP U s t eP d hL hzero e₀ y)) := by
  let z := α.app (op (AugmentedOrdered.CechCoordinates.topObject U m (cardinal (m := m))))
    ((show P.obj (op (AugmentedOrdered.CechCoordinates.topObject U m (cardinal (m := m)))) from
      KoszulPartial.Fractions.reciprocal R P U t ht (AugmentedOrdered.CechCoordinates.topIndex m (cardinal (m := m)))) *
      algebraMap R (P.obj (op (AugmentedOrdered.CechCoordinates.topObject U m (cardinal (m := m)))))
        ((RefinedScalarFraction.functional R P U s t eP k hP d hL hzero e₀ y)
          (TopExteriorCoordinates.generator
            (KoszulPartial.TopResidue.basis R (c := c) (m := m)))))
  have h := AugmentedOrdered.CechSingleTopCoordinates.topTotalClass_coordinates U N m
    (cardinal (m := m)) c z (CoefficientResidueClass.residueValue_closed R P U t ht N α
      (RefinedScalarFraction.functional R P U s t eP k hP d hL hzero e₀ y))
  simpa only [z, RefinedResidueClass.residueClass,
    CoefficientResidueClass.residueValue,
    AugmentedOrdered.CechSingleTopCoordinates.singleValue,
    RefinedScalarFraction.evaluation, scalarValue] using h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.RefinedResidueSingleCoordinates
