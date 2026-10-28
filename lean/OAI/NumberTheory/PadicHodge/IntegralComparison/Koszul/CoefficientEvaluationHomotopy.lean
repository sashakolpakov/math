import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.HomCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.SupportedCoefficientEvaluation

/-! # Coefficient Evaluation Homotopy -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.CoefficientEvaluationHomotopy

noncomputable section

/-! Actual augmentation-preserving coefficient maps give the weighted
point-evaluation homotopy on the entire coefficient presheaf. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Fractions OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Components OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Resolution
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  (R : Type u) [CommRing R] (P : Cᵒᵖ ⥤ CommAlgCat.{u} R)
  {c m : ℕ} (s : Fin c → R) (t : Fin m → R)
  (hs : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn s))
  (hst : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn (Fin.append s t)))
  (M : ModuleCat.{u} R) (PM : ProjectiveResolution M)
  (ε : M ⟶ ModuleCat.of R (R ⧸ KoszulPartial.Resolution.pointIdeal R s t))
  (β : ModuleCat.of R (R ⧸ KoszulPartial.Resolution.normalIdeal R s) ⟶ M)
  (a : PM.complex ⟶ (KoszulPartial.Resolution.pointResolution R s t hst).complex)
  (b : (KoszulPartial.Resolution.normalResolution R s hs).complex ⟶ PM.complex)
  (ha : a ≫ (KoszulPartial.Resolution.pointResolution R s t hst).π = PM.π ≫ (ChainComplex.single₀ _).map ε)
  (hb : b ≫ PM.π = (KoszulPartial.Resolution.normalResolution R s hs).π ≫ (ChainComplex.single₀ _).map β)
  (r : R) (hr : β ≫ ε = r • KoszulPartial.Resolution.quotient R s t)

 def chainHomotopy : Homotopy (b ≫ a) (r • KoszulPartial.Resolution.inclusion R s t) := by
  apply ProjectiveResolution.liftHomotopy (r • KoszulPartial.Resolution.quotient R s t)
  · rw [Category.assoc, ha, ← Category.assoc, hb, Category.assoc,
      ← Functor.map_comp, hr]
  · apply (ChainComplex.toSingle₀Equiv _ _).injective
    apply Subtype.ext
    change ((r • KoszulPartial.Resolution.inclusion R s t) ≫ (KoszulPartial.Resolution.pointResolution R s t hst).π).f 0 =
      ((KoszulPartial.Resolution.normalResolution R s hs).π ≫ (ChainComplex.single₀ (ModuleCat R)).map
        (r • KoszulPartial.Resolution.quotient R s t)).f 0
    have h := congrArg (fun z => z.f 0) (KoszulPartial.Resolution.augmentation R s t hs hst)
    simp only [HomologicalComplex.comp_f, ChainComplex.single₀_map_f_zero] at h ⊢
    change (r • (KoszulPartial.Resolution.inclusion R s t).f 0) ≫ (KoszulPartial.Resolution.pointResolution R s t hst).π.f 0 =
      (KoszulPartial.Resolution.normalResolution R s hs).π.f 0 ≫ (r • KoszulPartial.Resolution.quotient R s t)
    rw [Linear.smul_comp, Linear.comp_smul, h]

omit [HasFiniteProducts C] in
 theorem hom_map_comp {K L N : ChainComplex (ModuleCat.{u} R) ℕ} (f : K ⟶ L) (g : L ⟶ N) :
    HomCoefficientFunctor.map R (KoszulPartial.Fractions.modules R P) (f ≫ g) =
      HomCoefficientFunctor.map R (KoszulPartial.Fractions.modules R P) g ≫
        HomCoefficientFunctor.map R (KoszulPartial.Fractions.modules R P) f := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply NatTrans.ext
  funext v
  rfl

omit [HasFiniteProducts C] in
 theorem hom_map_smul {K L : ChainComplex (ModuleCat.{u} R) ℕ} (f : K ⟶ L) (w : R) :
    HomCoefficientFunctor.map R (KoszulPartial.Fractions.modules R P) (w • f) =
      w • HomCoefficientFunctor.map R (KoszulPartial.Fractions.modules R P) f := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply NatTrans.ext
  funext v
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro x
  exact φ.map_smul w _

 def pointMap : KoszulPartial.Components.coefficient R P (Fin.append s t) ⟶
    HomCoefficientFunctor.complex R (KoszulPartial.Fractions.modules R P) PM.complex :=
  (KoszulPoint.HomCoordinates.pointIso R P s t).inv ≫
    HomCoefficientFunctor.map R (KoszulPartial.Fractions.modules R P) a

 def evaluation : HomCoefficientFunctor.complex R (KoszulPartial.Fractions.modules R P) PM.complex ⟶
    KoszulPartial.Components.coefficient R P s := HomCoefficientFunctor.map R (KoszulPartial.Fractions.modules R P) b ≫
      (KoszulPoint.HomCoordinates.normalIso R P s).hom

 def homotopy : Homotopy
    (pointMap R P s t hst M PM a ≫ evaluation R P s hs M PM b)
    (r • DuplicateFraction.normalMap R s t P) := by
  let F := HomCoefficientFunctor.functor R (KoszulPartial.Fractions.modules R P)
  have h := F.mapHomotopy (chainHomotopy R s t hs hst M PM ε β a b ha hb r hr).op
  change Homotopy (HomCoefficientFunctor.map R (KoszulPartial.Fractions.modules R P) (b ≫ a))
    (HomCoefficientFunctor.map R (KoszulPartial.Fractions.modules R P) (r • KoszulPartial.Resolution.inclusion R s t)) at h
  rw [hom_map_comp, hom_map_smul] at h
  let h' := (h.compLeft (KoszulPoint.HomCoordinates.pointIso R P s t).inv).compRight
    (KoszulPoint.HomCoordinates.normalIso R P s).hom
  refine (Homotopy.ofEq (by simp only [pointMap, evaluation, Category.assoc])).trans
    (h'.trans (Homotopy.ofEq ?_))
  rw [Linear.comp_smul, Linear.smul_comp]
  apply congrArg (fun z => r • z)
  rw [Category.assoc, ← KoszulPoint.HomCoordinates.square, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.CoefficientEvaluationHomotopy
