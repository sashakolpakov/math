import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.Concentration
import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.ConcentrationNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechZeroIntersections

/-! # Concentration Forget -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.ConcentrationForget

noncomputable section

/-! Forgetting support commutes with the original concentration.
For a survivor vanishing on the punctured intersections this uniquely
normalizes every supported lift, without choosing a new point class. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyConcentration
open OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechForgetNaturality
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {R : Type u} [CommRing R] {ι : Type u} [LinearOrder ι] (U : ι → C)

def ambientFunctor (q : ℕ) : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} R) ℕ ⥤ ModuleCat.{u} R :=
  ((CategoryTheory.evaluation Cᵒᵖ (ModuleCat R)).obj (op (⊤_ C))).mapHomologicalComplex (.up ℕ) ⋙
    homologyFunctor (ModuleCat R) (.up ℕ) q

def forgetTransformation (q : ℕ) :
    CechHomotopyEquivalence.functor (R := R) U q ⟶ ambientFunctor (R := R) q where
  app K := homologyMap (AugmentedOrdered.CechForget.forgetSupport U K) q
  naturality _K _L a := AugmentedOrdered.CechForgetNaturality.homology U a q

variable (K : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} R) ℕ)
  (c : ℕ) (hK : ∀ q, q ≠ c → K.ExactAt q)

include hK in
theorem ambient_projection_isIso (q : ℕ) :
    IsIso ((ambientFunctor (R := R) (C := C) q).map (CohomologyConcentration.projection K c)) := by
  let : QuasiIso (CohomologyConcentration.projection K c) := CohomologyConcentration.projection_quasiIso K c hK
  let : QuasiIso (AugmentedOrdered.CechForgetNaturality.ambientMap (CohomologyConcentration.projection K c)) := by
    dsimp only [AugmentedOrdered.CechForgetNaturality.ambientMap]
    infer_instance
  change IsIso (homologyMap (AugmentedOrdered.CechForgetNaturality.ambientMap (CohomologyConcentration.projection K c)) q)
  infer_instance

include hK in
theorem ambient_inclusion_isIso (q : ℕ) :
    IsIso ((ambientFunctor (R := R) (C := C) q).map (CohomologyConcentration.inclusion K c)) := by
  let : QuasiIso (CohomologyConcentration.inclusion K c) := CohomologyConcentration.inclusion_quasiIso K c hK
  let : QuasiIso (AugmentedOrdered.CechForgetNaturality.ambientMap (CohomologyConcentration.inclusion K c)) := by
    dsimp only [AugmentedOrdered.CechForgetNaturality.ambientMap]
    infer_instance
  change IsIso (homologyMap (AugmentedOrdered.CechForgetNaturality.ambientMap (CohomologyConcentration.inclusion K c)) q)
  infer_instance

def ambientIso (q : ℕ) : (ambientFunctor q).obj K ≅
    (ambientFunctor q).obj ((single _ (.up ℕ) c).obj (K.homology c)) := by
  letI := ambient_projection_isIso K c hK q
  letI := ambient_inclusion_isIso K c hK q
  exact Functor.ConcentrationSingle.iso (ambientFunctor q) K c

theorem square (q : ℕ) :
    (AugmentedCech.Concentration.iso U K c hK q).hom ≫
        homologyMap (AugmentedOrdered.CechForget.forgetSupport U ((single _ (.up ℕ) c).obj (K.homology c))) q =
      homologyMap (AugmentedOrdered.CechForget.forgetSupport U K) q ≫ (ambientIso K c hK q).hom := by
  let := AugmentedCech.Concentration.projection_isIso U K c hK q
  let := AugmentedCech.Concentration.inclusion_isIso U K c hK q
  let := ambient_projection_isIso K c hK q
  let := ambient_inclusion_isIso K c hK q
  exact Functor.ConcentrationNaturality.square
    (CechHomotopyEquivalence.functor U q) (ambientFunctor q)
    (forgetTransformation U q) K c

variable (hzero : ∀ p q, 0 < q → ∀ a : AugmentedOrdered.Cech.Index ι q,
    IsZero ((((single (Cᵒᵖ ⥤ ModuleCat R) (.up ℕ) c).obj (K.homology c)).X p).obj
      (op ((AugmentedOrdered.Cech.formal U q).obj a))))

def survivorForgetIso (q : ℕ) := homologyMapIso
  (AugmentedOrdered.CechZeroIntersections.iso U
    ((single _ (.up ℕ) c).obj (K.homology c)) hzero) q

theorem lift_normalization (q : ℕ) {T : ModuleCat.{u} R}
    (l : T ⟶ (CechHomotopyEquivalence.functor U q).obj K)
    (a : T ⟶ (ambientFunctor q).obj K)
    (hl : l ≫ homologyMap (AugmentedOrdered.CechForget.forgetSupport U K) q = a) :
    l ≫ (AugmentedCech.Concentration.iso U K c hK q).hom =
      a ≫ (ambientIso K c hK q).hom ≫ (survivorForgetIso U K c hzero q).inv := by
  apply (cancel_mono (survivorForgetIso U K c hzero q).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change l ≫ ((AugmentedCech.Concentration.iso U K c hK q).hom ≫
    homologyMap (AugmentedOrdered.CechForget.forgetSupport U ((single _ (.up ℕ) c).obj (K.homology c))) q) = _
  rw [square U K c hK q, ← Category.assoc, hl]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.ConcentrationForget
