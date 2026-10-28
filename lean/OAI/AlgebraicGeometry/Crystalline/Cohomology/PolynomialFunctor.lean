import OAI.AlgebraicGeometry.Crystalline.Cohomology.PolynomialThickening
import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.BaseChange
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Site

/-! # Polynomial Functor -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.PolynomialFunctor.CrystallinePolynomialFunctor

noncomputable section

/-!
# Polynomial PD extensions on the native crystalline site

The actual extension by divided coordinates is functorial in every
crystalline morphism, including changes of residual affine open. Its
projection and zero section are natural transformations on the native
site, and the zero section followed by projection is the identity.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) (σ : Type u)

local notation "W" => WittVector p k

def object (Q : Site.Object p k X) : Site.Object p k X where
  residueRing := Q.residueRing
  thickening := PolynomialThickening.CrystallinePolynomialThickening.thickening p k Q.residueRing σ Q.thickening
  immersion := Q.immersion
  over_base := Q.over_base

instance objectRelativeAlgebra (Q : Site.Object p k X) :
    Algebra Q.thickening.ring (object p k X σ Q).thickening.ring :=
  PolynomialThickening.CrystallinePolynomialThickening.thickeningRelativeAlgebra p k Q.residueRing σ Q.thickening

variable {p k X} {Q P U : Site.Object p k X}

def ambientMap (f : Q ⟶ P) : (object p k X σ P).thickening.ring →ₐ[W]
    (object p k X σ Q).thickening.ring := by
  have ht (w : W) := IsScalarTower.algebraMap_apply W Q.thickening.ring
    (DividedPowerAlgebra Q.thickening.ring (σ →₀ Q.thickening.ring)) w
  letI : Algebra P.thickening.ring Q.thickening.ring := f.ambientMap.toRingHom.toAlgebra
  let g := Divided.AlgebraBaseChange.DividedAlgebraBaseChange.map P.thickening.ring Q.thickening.ring σ
  refine { __ := g.toRingHom, commutes' := ?_ }
  intro w
  change g (algebraMap W (DividedPowerAlgebra P.thickening.ring (σ →₀ P.thickening.ring)) w) = _
  rw [IsScalarTower.algebraMap_apply W P.thickening.ring _, Divided.AlgebraBaseChange.DividedAlgebraBaseChange.map_coefficient]
  have hc : algebraMap P.thickening.ring Q.thickening.ring (algebraMap W P.thickening.ring w) =
      algebraMap W Q.thickening.ring w := f.ambientMap.commutes w
  rw [hc]
  exact (ht w).symm

theorem ambientMap_coefficient (f : Q ⟶ P) (a : P.thickening.ring) :
    CrystallinePolynomialFunctor.ambientMap σ f (algebraMap P.thickening.ring
      (DividedPowerAlgebra P.thickening.ring (σ →₀ P.thickening.ring)) a) =
        algebraMap Q.thickening.ring
          (DividedPowerAlgebra Q.thickening.ring (σ →₀ Q.thickening.ring)) (f.ambientMap a) := by
  let : Algebra P.thickening.ring Q.thickening.ring := f.ambientMap.toRingHom.toAlgebra
  exact Divided.AlgebraBaseChange.DividedAlgebraBaseChange.map_coefficient P.thickening.ring Q.thickening.ring σ a

theorem ambientMap_generator (f : Q ⟶ P) (n : ℕ) (i : σ) :
    CrystallinePolynomialFunctor.ambientMap σ f (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator P.thickening.ring σ n i) =
      Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator Q.thickening.ring σ n i := by
  let : Algebra P.thickening.ring Q.thickening.ring := f.ambientMap.toRingHom.toAlgebra
  exact Divided.AlgebraBaseChange.DividedAlgebraBaseChange.map_generator P.thickening.ring Q.thickening.ring σ n i

theorem augmentation_ambientMap (f : Q ⟶ P) (a : (object p k X σ P).thickening.ring) :
    Multivariable.Reduction.MultivariableReduction.augmentation Q.thickening.ring σ (CrystallinePolynomialFunctor.ambientMap σ f a) =
      f.ambientMap (Multivariable.Reduction.MultivariableReduction.augmentation P.thickening.ring σ a) := by
  let : Algebra P.thickening.ring Q.thickening.ring := f.ambientMap.toRingHom.toAlgebra
  exact Divided.AlgebraBaseChange.DividedAlgebraBaseChange.augmentation_map P.thickening.ring Q.thickening.ring σ a

theorem ambientMap_isDPMorphism (f : Q ⟶ P) :
    DividedPowers.IsDPMorphism (object p k X σ P).thickening.dividedPowers
      (object p k X σ Q).thickening.dividedPowers (CrystallinePolynomialFunctor.ambientMap σ f).toRingHom := by
  let : Algebra P.thickening.ring Q.thickening.ring := f.ambientMap.toRingHom.toAlgebra
  have hd := FreeRelative.BaseChange.FreeRelativeBaseChange.map_isDPMorphism P.thickening.ring Q.thickening.ring σ
    (RingHom.ker P.thickening.reduction) P.thickening.dividedPowers
    (RingHom.ker Q.thickening.reduction) Q.thickening.dividedPowers f.dp_comp
  exact (PolynomialThickening.CrystallinePolynomialThickening.identity_isDPMorphism p k Q.residueRing σ Q.thickening).comp _
    (hd.comp _ (PolynomialThickening.CrystallinePolynomialThickening.identity_inverse_isDPMorphism
      p k P.residueRing σ P.thickening))

def map (f : Q ⟶ P) : object p k X σ Q ⟶ object p k X σ P where
  reducedMap := f.reducedMap
  ambientMap := CrystallinePolynomialFunctor.ambientMap σ f
  reduction_comm a := by
    change Q.thickening.reduction (Multivariable.Reduction.MultivariableReduction.augmentation Q.thickening.ring σ
      (CrystallinePolynomialFunctor.ambientMap σ f a)) = f.reducedMap (P.thickening.reduction
        (Multivariable.Reduction.MultivariableReduction.augmentation P.thickening.ring σ a))
    rw [augmentation_ambientMap, f.reduction_comm]
  over_X := f.over_X
  dp_comp := ambientMap_isDPMorphism σ f

theorem map_id (Q : Site.Object p k X) : CrystallinePolynomialFunctor.map σ (𝟙 Q) = 𝟙 (object p k X σ Q) := by
  apply Site.Object.Hom.ext
  · rfl
  · have he : (CrystallinePolynomialFunctor.map σ (𝟙 Q)).ambientMap.toRingHom =
        RingHom.id (object p k X σ Q).thickening.ring := by
      apply FreeRelative.BaseChange.FreeRelativeBaseChange.ringHom_ext Q.thickening.ring σ
      · intro a
        exact ambientMap_coefficient σ (𝟙 Q) a
      · intro n i
        exact ambientMap_generator σ (𝟙 Q) n i
    exact AlgHom.ext (RingHom.congr_fun he)

theorem map_comp (f : Q ⟶ P) (g : P ⟶ U) : CrystallinePolynomialFunctor.map σ (f ≫ g) = CrystallinePolynomialFunctor.map σ f ≫ CrystallinePolynomialFunctor.map σ g := by
  apply Site.Object.Hom.ext
  · rfl
  · have he : (CrystallinePolynomialFunctor.map σ (f ≫ g)).ambientMap.toRingHom =
        (CrystallinePolynomialFunctor.map σ f ≫ CrystallinePolynomialFunctor.map σ g).ambientMap.toRingHom := by
      apply FreeRelative.BaseChange.FreeRelativeBaseChange.ringHom_ext U.thickening.ring σ
      · intro a
        exact (ambientMap_coefficient σ (f ≫ g) a).trans
          ((congrArg (CrystallinePolynomialFunctor.ambientMap σ f) (ambientMap_coefficient σ g a)).trans
            (ambientMap_coefficient σ f (g.ambientMap a))).symm
      · intro n i
        change CrystallinePolynomialFunctor.ambientMap σ (f ≫ g) (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator U.thickening.ring σ n i) =
          CrystallinePolynomialFunctor.ambientMap σ f (CrystallinePolynomialFunctor.ambientMap σ g (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator U.thickening.ring σ n i))
        rw [ambientMap_generator, ambientMap_generator, ambientMap_generator]
    exact AlgHom.ext (RingHom.congr_fun he)

variable (p k X)

/-- Adjoining divided coordinates is an actual endofunctor of the native crystalline site. -/
def functor : Site.Object p k X ⥤ Site.Object p k X where
  obj := object p k X σ
  map := CrystallinePolynomialFunctor.map σ
  map_id := CrystallinePolynomialFunctor.map_id σ
  map_comp := CrystallinePolynomialFunctor.map_comp σ

def projection : functor p k X σ ⟶ 𝟭 (Site.Object p k X) where
  app Q :=
    { reducedMap := AlgHom.id k Q.residueRing
      ambientMap := (PolynomialThickening.CrystallinePolynomialThickening.inclusion p k Q.residueRing σ Q.thickening).hom
      reduction_comm a := DFunLike.congr_fun
        (PolynomialThickening.CrystallinePolynomialThickening.inclusion p k Q.residueRing σ Q.thickening).reduction_comp a
      over_X := by change Spec.map (𝟙 _) ≫ Q.immersion = Q.immersion; simp
      dp_comp := (PolynomialThickening.CrystallinePolynomialThickening.inclusion p k Q.residueRing σ Q.thickening).dp_comp }
  naturality {Q P} f := by
    apply Site.Object.Hom.ext
    · ext; rfl
    · ext a
      exact ambientMap_coefficient σ f a

def zeroSection : 𝟭 (Site.Object p k X) ⟶ functor p k X σ where
  app Q :=
    { reducedMap := AlgHom.id k Q.residueRing
      ambientMap := (PolynomialThickening.CrystallinePolynomialThickening.augmentation p k Q.residueRing σ Q.thickening).hom
      reduction_comm _ := rfl
      over_X := by change Spec.map (𝟙 _) ≫ Q.immersion = Q.immersion; simp
      dp_comp := (PolynomialThickening.CrystallinePolynomialThickening.augmentation p k Q.residueRing σ Q.thickening).dp_comp }
  naturality {Q P} f := by
    apply Site.Object.Hom.ext
    · ext; rfl
    · ext a
      exact (augmentation_ambientMap σ f a).symm

theorem zeroSection_projection : zeroSection p k X σ ≫ projection p k X σ = 𝟙 _ := by
  apply NatTrans.ext
  funext Q
  apply Site.Object.Hom.ext
  · ext; rfl
  · ext a
    exact (Multivariable.Reduction.MultivariableReduction.augmentation Q.thickening.ring σ).commutes a

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.PolynomialFunctor.CrystallinePolynomialFunctor
