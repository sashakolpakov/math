import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.Poincare
import OAI.NumberTheory.PadicHodge.IntegralComparison.Free.RelativeFormBasis
import OAI.NumberTheory.PadicHodge.IntegralComparison.PD.ConstantShifts

/-! # Basis -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.Basis

noncomputable section

/-!
# IntegralComparison: bases of actual relative forms from divided-coordinate identifications
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.FormData OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.Poincare

universe u v w

variable {C : Type v} [Category.{w} C] {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)}
  (H Q : C ⥤ BigCrystallineSite.Object p B J δ f) (π : H ⟶ Q) (σ : Type u) [LinearOrder σ] (U : C)
  (e : Crystalline.DividedCoordinates.object (Q.obj U) σ ≅ H.obj U)
  (he : e.hom ≫ π.app U = Crystalline.DividedCoordinates.projection (Q.obj U) σ)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite.Object.ring (Q.obj U)
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.DividedCoordinates.object (Q.obj U) σ

def generator (i : σ) : (G).ring := AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i

def basis (n : ℕ) : Module.Basis (Set.powersetCard σ n) (H.obj U).ring (FormData.Forms H Q π U n) := by
  letI : Algebra R (H.obj U).ring := FormData.relativeAlgebra H Q π U
  exact PD.FormBasisTransport.basis R (G).ring (H.obj U).ring (G).ideal (G).dividedPowers
    (H.obj U).ideal (H.obj U).dividedPowers (Poincare.freeAlgEquiv H Q π σ U e he).symm
    e.inv.ringMap.isDPMorphism e.hom.ringMap.isDPMorphism n
    (Free.RelativeFormBasis.formBasis R σ (Q.obj U).ideal (Q.obj U).dividedPowers n)

theorem formsEquiv_basis (n : ℕ) (s : Set.powersetCard σ n) :
    Poincare.formsEquiv H Q π σ U e he n (basis H Q π σ U e he n s) =
      Free.RelativeFormBasis.formBasis R σ (Q.obj U).ideal (Q.obj U).dividedPowers n s := by
  let : Algebra R (H.obj U).ring := FormData.relativeAlgebra H Q π U
  have hb := PD.FormBasisTransport.basis_apply R (G).ring (H.obj U).ring (G).ideal (G).dividedPowers
    (H.obj U).ideal (H.obj U).dividedPowers (Poincare.freeAlgEquiv H Q π σ U e he).symm
    e.inv.ringMap.isDPMorphism e.hom.ringMap.isDPMorphism n
    (Free.RelativeFormBasis.formBasis R σ (Q.obj U).ideal (Q.obj U).dividedPowers n) s
  exact (congrArg (Poincare.formsEquiv H Q π σ U e he n) hb).trans
    (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamEquivalence.PDDeRhamEquivalence.formMap_inverse (A := CommAlgCat.of R (G).ring)
      (B := CommAlgCat.of R (H.obj U).ring) (Poincare.freeAlgEquiv H Q π σ U e he).symm
      e.inv.ringMap.isDPMorphism e.hom.ringMap.isDPMorphism n _)

theorem basis_eq_symbol (v : σ → (H.obj U).ring) (a : σ → R)
    (hv : ∀ i, e.hom.ringMap (v i) = algebraMap R (G).ring (a i) +
      generator Q σ U i)
    (n : ℕ) (s : Set.powersetCard σ n) :
    basis H Q π σ U e he n s = FormData.symbol H Q π U n 1 (fun j => v (Set.powersetCard.ofFinEmbEquiv.symm s j)) := by
  apply (Poincare.formsEquiv H Q π σ U e he n).injective
  refine (formsEquiv_basis H Q π σ U e he n s).trans ?_
  refine Eq.trans ?_ (Poincare.formsEquiv_symbol H Q π σ U e he n 1
    (fun j => v (Set.powersetCard.ofFinEmbEquiv.symm s j))).symm
  have h1 : e.hom.ringMap (1 : (H.obj U).ring) = (1 : (G).ring) := e.hom.ringMap.toRingHom.map_one
  have ht : (fun j => e.hom.ringMap (v (Set.powersetCard.ofFinEmbEquiv.symm s j))) =
      (fun j => algebraMap R (G).ring (a (Set.powersetCard.ofFinEmbEquiv.symm s j)) +
        generator Q σ U (Set.powersetCard.ofFinEmbEquiv.symm s j)) :=
    funext (fun j => hv (Set.powersetCard.ofFinEmbEquiv.symm s j))
  have hs := congrArg₂ (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R (G).ring (G).ideal (G).dividedPowers) h1 ht
  exact (Free.RelativeFormBasis.formBasis_apply R σ (Q.obj U).ideal (Q.obj U).dividedPowers n s).trans
    ((PD.ConstantShifts.symbol_base_add R (G).ring (G).ideal (G).dividedPowers 1
      (fun j => generator Q σ U (Set.powersetCard.ofFinEmbEquiv.symm s j))
      (fun j => a (Set.powersetCard.ofFinEmbEquiv.symm s j))).symm.trans hs.symm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.Basis
