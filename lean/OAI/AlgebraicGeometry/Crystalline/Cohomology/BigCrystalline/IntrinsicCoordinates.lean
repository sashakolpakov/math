import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicLifts
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameFunctor
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Operators
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.Translations

/-! # Intrinsic Coordinates -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicCoordinates.BigCrystallineIntrinsicCoordinates

noncomputable section

/-! # Actual coordinate translations identify big and native frame functions -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicLifts.BigCrystallineIntrinsicLifts OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] (a : σ → B)

local notation "W" => WittVector p k
local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "I" => Ideal.span {(p : W)}
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "bX" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k X
local notation "j" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicLifts.BigCrystallineIntrinsicLifts.inclusion p k B

def rawEquiv (Q : Site.Object p k X) :
    DividedPowerAlgebra Q.thickening.ring (σ →₀ Q.thickening.ring) ≃ₐ[Q.thickening.ring]
      DividedPowerAlgebra Q.thickening.ring (σ →₀ Q.thickening.ring) :=
  Divided.Translations.DividedTranslations.algebraEquiv Q.thickening.ring σ (RingHom.ker Q.thickening.reduction)
    Q.thickening.dividedPowers (IntrinsicLifts.BigCrystallineIntrinsicLifts.difference p k B σ a Q) (IntrinsicLifts.BigCrystallineIntrinsicLifts.difference_mem p k B σ a Q)

theorem rawEquiv_isDPMorphism (Q : Site.Object p k X) :
    DividedPowers.IsDPMorphism
      (FreeRelative.Powers.FreeRelativePowers.dividedPowers Q.thickening.ring σ
        (RingHom.ker Q.thickening.reduction) Q.thickening.dividedPowers)
      (FreeRelative.Powers.FreeRelativePowers.dividedPowers Q.thickening.ring σ
        (RingHom.ker Q.thickening.reduction) Q.thickening.dividedPowers)
      (rawEquiv p k B σ a Q).toRingHom :=
  Divided.Translations.DividedTranslations.algebraEquiv_isDPMorphism Q.thickening.ring σ
    (RingHom.ker Q.thickening.reduction) Q.thickening.dividedPowers
    (IntrinsicLifts.BigCrystallineIntrinsicLifts.difference p k B σ a Q) (IntrinsicLifts.BigCrystallineIntrinsicLifts.difference_mem p k B σ a Q)

theorem rawEquiv_coordinate (Q : Site.Object p k X) (i : σ) :
    rawEquiv p k B σ a Q (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator Q.thickening.ring σ 1 i) =
      algebraMap Q.thickening.ring (DividedPowerAlgebra Q.thickening.ring (σ →₀ Q.thickening.ring))
        (IntrinsicLifts.BigCrystallineIntrinsicLifts.difference p k B σ a Q i) + Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator Q.thickening.ring σ 1 i :=
  Divided.Translations.DividedTranslations.map_coordinate Q.thickening.ring σ (RingHom.ker Q.thickening.reduction)
    Q.thickening.dividedPowers (IntrinsicLifts.BigCrystallineIntrinsicLifts.difference p k B σ a Q) (IntrinsicLifts.BigCrystallineIntrinsicLifts.difference_mem p k B σ a Q) i

def functions : (Site.Object p k X)ᵒᵖ ⥤ ModuleCat W :=
  (j).op ⋙ FrameFunctor.BigCrystallineFrameFunctor.functions (p := p) (J := I) (δ := γ) (base := bX) a

def component (Q : Site.Object p k X) : (functions p k B σ a).obj (op Q) ≃ₗ[W]
    (CrystallineFrame.Operators.CrystallineFrameOperators.functions p k B σ a).obj (op Q) := by
  let M := (functions p k B σ a).obj (op Q)
  let N := (CrystallineFrame.Operators.CrystallineFrameOperators.functions p k B σ a).obj (op Q)
  let : Module Q.thickening.ring M := inferInstanceAs
    (Module Q.thickening.ring (DividedPowerAlgebra Q.thickening.ring (σ →₀ Q.thickening.ring)))
  let : Module Q.thickening.ring N := inferInstanceAs
    (Module Q.thickening.ring (DividedPowerAlgebra Q.thickening.ring (σ →₀ Q.thickening.ring)))
  let : IsScalarTower W Q.thickening.ring M := by
    apply IsScalarTower.of_algebraMap_smul
    intro w x
    let xb : DividedPowerAlgebra ((j).obj Q).ring (σ →₀ ((j).obj Q).ring) := x
    exact IsScalarTower.algebraMap_smul ((j).obj Q).ring w xb
  let : IsScalarTower W Q.thickening.ring N := by
    apply IsScalarTower.of_algebraMap_smul
    intro w x
    let xn : DividedPowerAlgebra Q.thickening.ring (σ →₀ Q.thickening.ring) := x
    let xt : (CrystallineFrame.Map.CrystallineFrameMap.object p k B σ Q).thickening.ring := x
    have h₁ := Algebra.smul_def (algebraMap W Q.thickening.ring w) xn
    have h₂ := Algebra.smul_def w xt
    have h := IsScalarTower.algebraMap_apply W Q.thickening.ring
      (DividedPowerAlgebra Q.thickening.ring (σ →₀ Q.thickening.ring)) w
    exact h₁.trans ((congrArg (fun z : DividedPowerAlgebra Q.thickening.ring
      (σ →₀ Q.thickening.ring) => z * xn) h.symm).trans h₂.symm)
  let e : M ≃ₗ[Q.thickening.ring] N := (rawEquiv p k B σ a Q).toLinearEquiv
  exact e.restrictScalars W

def bigMap {Q P : Site.Object p k X} (f : Q ⟶ P) :
    DividedPowerAlgebra P.thickening.ring (σ →₀ P.thickening.ring) →+*
      DividedPowerAlgebra Q.thickening.ring (σ →₀ Q.thickening.ring) :=
  (FrameMaps.BigCrystallineFrameMaps.ambientMap a ((j).map f)).toRingHom

theorem bigMap_coefficient {Q P : Site.Object p k X} (f : Q ⟶ P) (t : P.thickening.ring) :
    bigMap p k B σ a f (algebraMap P.thickening.ring _ t) =
      algebraMap Q.thickening.ring _ (f.ambientMap t) := by
  exact FrameMaps.BigCrystallineFrameMaps.ambientMap_coefficient a ((j).map f) t

theorem bigMap_coordinate {Q P : Site.Object p k X} (f : Q ⟶ P) (i : σ) :
    bigMap p k B σ a f (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator P.thickening.ring σ 1 i) =
      algebraMap Q.thickening.ring _ (IntrinsicLifts.BigCrystallineIntrinsicLifts.lift p k B σ a Q i - f.ambientMap (IntrinsicLifts.BigCrystallineIntrinsicLifts.lift p k B σ a P i)) +
        Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator Q.thickening.ring σ 1 i := by
  exact FrameMaps.BigCrystallineFrameMaps.ambientMap_coordinate a ((j).map f) i

theorem naturality {Q P : Site.Object p k X} (f : Q ⟶ P) :
    (rawEquiv p k B σ a Q).toRingHom.comp (bigMap p k B σ a f) =
      (CrystallineFrame.Map.CrystallineFrameMap.ambientMap a f).toRingHom.comp (rawEquiv p k B σ a P).toRingHom := by
  apply Divided.AffineMaps.DividedAffineMaps.ringHom_ext_of_coordinate P.thickening.ring σ
    (RingHom.ker P.thickening.reduction) P.thickening.dividedPowers
    (DividedPowerAlgebra Q.thickening.ring (σ →₀ Q.thickening.ring))
    (Multivariable.DividedPowers.MultivariableDividedPowers.ideal Q.thickening.ring σ (RingHom.ker Q.thickening.reduction))
    (FreeRelative.Powers.FreeRelativePowers.dividedPowers Q.thickening.ring σ
      (RingHom.ker Q.thickening.reduction) Q.thickening.dividedPowers)
    _ _ ((rawEquiv_isDPMorphism p k B σ a Q).comp _
      (FrameMaps.BigCrystallineFrameMaps.ambientMap_relativePD a ((j).map f)))
    ((CrystallineFrame.Map.CrystallineFrameMap.ambientMap_relativePD a f).comp _ (rawEquiv_isDPMorphism p k B σ a P))
  · intro t
    change rawEquiv p k B σ a Q
      (bigMap p k B σ a f (algebraMap P.thickening.ring _ t)) =
        CrystallineFrame.Map.CrystallineFrameMap.ambientMap a f (rawEquiv p k B σ a P (algebraMap P.thickening.ring _ t))
    rw [bigMap_coefficient, AlgEquiv.commutes, AlgEquiv.commutes,
      CrystallineFrame.Map.CrystallineFrameMap.ambientMap_coefficient]
  · intro i
    change rawEquiv p k B σ a Q
      (bigMap p k B σ a f (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator P.thickening.ring σ 1 i)) =
        CrystallineFrame.Map.CrystallineFrameMap.ambientMap a f (rawEquiv p k B σ a P (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator P.thickening.ring σ 1 i))
    rw [bigMap_coordinate, map_add, AlgEquiv.commutes,
      rawEquiv_coordinate, rawEquiv_coordinate, map_add,
      CrystallineFrame.Map.CrystallineFrameMap.ambientMap_coefficient, CrystallineFrame.Map.CrystallineFrameMap.ambientMap_coordinate]
    change algebraMap Q.thickening.ring _
        (IntrinsicLifts.BigCrystallineIntrinsicLifts.lift p k B σ a Q i - f.ambientMap (IntrinsicLifts.BigCrystallineIntrinsicLifts.lift p k B σ a P i)) +
      (algebraMap Q.thickening.ring _
        (CrystallineFrame.Lifts.CrystallineFrameLifts.lift p k B σ a Q i - IntrinsicLifts.BigCrystallineIntrinsicLifts.lift p k B σ a Q i) + Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator Q.thickening.ring σ 1 i) =
      algebraMap Q.thickening.ring _
        (f.ambientMap (CrystallineFrame.Lifts.CrystallineFrameLifts.lift p k B σ a P i - IntrinsicLifts.BigCrystallineIntrinsicLifts.lift p k B σ a P i)) +
      (algebraMap Q.thickening.ring _
        (CrystallineFrame.Lifts.CrystallineFrameLifts.lift p k B σ a Q i - f.ambientMap (CrystallineFrame.Lifts.CrystallineFrameLifts.lift p k B σ a P i)) +
          Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator Q.thickening.ring σ 1 i)
    simp only [map_sub]
    abel

def iso : functions p k B σ a ≅ CrystallineFrame.Operators.CrystallineFrameOperators.functions p k B σ a :=
  NatIso.ofComponents (fun Q => (component p k B σ a Q.unop).toModuleIso) (by
    intro Q P f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    exact RingHom.congr_fun (naturality p k B σ a f.unop) t)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicCoordinates.BigCrystallineIntrinsicCoordinates
