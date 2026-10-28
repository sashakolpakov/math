import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.PartialClass
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechTopNaturality

/-! # Coefficient Residue -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.CoefficientResidue

noncomputable section

/-! Evaluation on the oriented normal wedge maps the actual Hom Koszul
complex to coefficients killed by the normal equations. It sends mixed
point fractions to their literal coefficient residue. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Fractions OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Components OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechTopNaturality
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  (R : Type u) [CommRing R] (P : Cᵒᵖ ⥤ CommAlgCat.{u} R)
  {c : ℕ} (s : Fin c → R)
  (N : Cᵒᵖ ⥤ ModuleCat.{u} R) (α : KoszulPartial.Fractions.modules R P ⟶ N)
  (hN : ∀ (a : Cᵒᵖ) (i : Fin c) (x : N.obj a), s i • x = 0)

def evaluation : (KoszulPartial.Components.coefficient R P s).X c ⟶ N where
  app a := ModuleCat.ofHom
    { toFun φ := α.app a (φ (TopExteriorCoordinates.generator (Pi.basisFun R (Fin c))))
      map_add' := by
        intro φ ψ
        change (α.app a).hom (φ _ + ψ _) = _
        exact (α.app a).hom.map_add _ _
      map_smul' := by
        intro r φ
        change (α.app a).hom (r • φ _) = _
        exact (α.app a).hom.map_smul r _ }
  naturality a b f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    change (⋀[R]^c (KoszulPartial.Fractions.normal R (c := c))) →ₗ[R] P.obj a at φ
    exact ConcreteCategory.congr_hom (α.naturality f)
      (φ (TopExteriorCoordinates.generator (Pi.basisFun R (Fin c))))

include hN in
omit [HasFiniteProducts C] in
theorem boundary (i : ℕ) (hi : (ComplexShape.up ℕ).Rel i c) :
    (KoszulPartial.Components.coefficient R P s).d i c ≫ evaluation R P s N α = 0 := by
  obtain rfl : c = i + 1 := hi.symm
  apply NatTrans.ext
  funext a
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  change (⋀[R]^i (KoszulPartial.Fractions.normal R (c := i + 1))) →ₗ[R] P.obj a at φ
  dsimp only [KoszulPartial.Components.coefficient, HomPresheaf.complex]
  rw [CochainComplex.of_d]
  change α.app a (φ (AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction R _
    (GeneratorMatrix.equation R s) i
      (TopExteriorCoordinates.generator (Pi.basisFun R (Fin (i + 1)))))) = 0
  rw [TopBoundary.contraction_sum, map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro j _
  rw [φ.map_smul, (α.app a).hom.map_smul]
  exact hN a j _

def complexMap : KoszulPartial.Components.coefficient R P s ⟶ (single (Cᵒᵖ ⥤ ModuleCat R) (.up ℕ) c).obj N :=
  mkHomToSingle (evaluation R P s N α) (boundary R P s N α hN)

omit [HasFiniteProducts C] in
theorem complexMap_top : (complexMap R P s N α hN).f c ≫
    (singleObjXSelf (.up ℕ) c N).hom = evaluation R P s N α := by
  simp [complexMap]

variable {m : ℕ} (U : ULift.{u} (Fin m) → C) (t : Fin m → R)
  (ht : ∀ i, IsUnit (algebraMap R (P.obj (op (U i))) (t i.down)))

theorem fraction (a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) m)
    (φ : Module.Dual R (⋀[R]^(c + m) (KoszulPartial.Fractions.ambient R (c := c) (m := m)))) :
    (evaluation R P s N α).app (op ((AugmentedOrdered.Cech.formal U m).obj a))
      (KoszulPartial.Components.coordinateAt R P U t ht (c + m) c m rfl a φ) =
    α.app (op ((AugmentedOrdered.Cech.formal U m).obj a))
      (KoszulPartial.Fractions.reciprocal R P U t ht a * algebraMap R (P.obj (op ((AugmentedOrdered.Cech.formal U m).obj a)))
        (φ (TopExteriorCoordinates.generator
          (KoszulPartial.TopResidue.basis R (c := c) (m := m))))) :=
  congrArg (α.app (op ((AugmentedOrdered.Cech.formal U m).obj a)))
    (KoszulPartial.PartialClass.coefficient R P U t ht φ a)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.CoefficientResidue
