import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.EvenAlgebra
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.EvenAppend
import OAI.AlgebraicGeometry.HodgeConjecture.CupRegrouping
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.CupAppend

/-! # Packed Regroup -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.CMReduction.PackedRegroup.CM.Construction

/-! Degree-aware packaging of actual cup products and pullbacks. The fixed
four-vector identity gives the exact regrouping used in a pair switch. -/

open _root_.CategoryTheory

def packEven (X : TopCat.{0}) (p : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) X (p + p)) : EvenAlgebra.CM.Construction.EvenClass (R := ℂ) X := ⟨p, a⟩

theorem packEven_injective (X : TopCat.{0}) (p : ℕ) : Function.Injective (packEven X p) := by
  intro a b h
  exact eq_of_heq (Sigma.mk.inj h).2

def IsAlgebraicEven (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (a : EvenAlgebra.CM.Construction.EvenClass (R := ℂ) (Betti.Scheme.schemePointSpace V.toOver)) :
    Prop := a.2 ∈ V.complexGeometricAlgebraicClasses a.1

theorem IsAlgebraicEven.mul (h_LineBundleCycles : CycleOperations.CM.Construction.LineBundleCyclesInput) (h_ThomClass : CycleOperations.CM.Construction.ExteriorInput)
    {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    {a b : EvenAlgebra.CM.Construction.EvenClass (R := ℂ) (Betti.Scheme.schemePointSpace V.toOver)}
    (ha : IsAlgebraicEven V a) (hb : IsAlgebraicEven V b) : IsAlgebraicEven V (a * b) :=
  ComplexOperations.CM.Construction.complex_cup_algebraic h_LineBundleCycles h_ThomClass V a.1 b.1 a.2 b.2 ha hb

theorem scheme_pullback_cohomologyCast {R : Type} [CommRing R]
    {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) {n m : ℕ} (h : n = m)
    (a : Betti.Scheme.schemeBetti (ModuleCat.of R R) Y n) :
    Betti.Scheme.schemeBettiMap (ModuleCat.of R R) m f
      (AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCast (TopCat.toSSet.obj (Betti.Scheme.schemePointSpace Y)) (ModuleCat.of R R) h a) =
    AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCast (TopCat.toSSet.obj (Betti.Scheme.schemePointSpace X)) (ModuleCat.of R R) h
      (Betti.Scheme.schemeBettiMap (ModuleCat.of R R) n f a) := by
  subst m
  rfl

theorem evenCup_pullback {R : Type} [CommRing R]
    {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) (p q : ℕ)
    (a : Betti.Scheme.schemeBetti (ModuleCat.of R R) Y (p + p))
    (b : Betti.Scheme.schemeBetti (ModuleCat.of R R) Y (q + q)) :
    Betti.Scheme.schemeBettiMap (ModuleCat.of R R) ((p + q) + (p + q)) f
      (ComplexOperations.CM.Construction.evenCup R (Betti.Scheme.schemePointSpace Y) p q a b) =
    ComplexOperations.CM.Construction.evenCup R (Betti.Scheme.schemePointSpace X) p q
      (Betti.Scheme.schemeBettiMap (ModuleCat.of R R) (p + p) f a)
      (Betti.Scheme.schemeBettiMap (ModuleCat.of R R) (q + q) f b) := by
  change Betti.Scheme.schemeBettiMap (ModuleCat.of R R) _ f (AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCast _ _ _ _) = _
  rw [scheme_pullback_cohomologyCast (R := R) f (add_add_add_comm p p q q),
    CupPullback.CM.Construction.scheme_cup_pullback]
  rfl

def evenPullback {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) :
    MulHom (EvenAlgebra.CM.Construction.EvenClass (R := ℂ) (Betti.Scheme.schemePointSpace Y)) (EvenAlgebra.CM.Construction.EvenClass (R := ℂ) (Betti.Scheme.schemePointSpace X)) where
  toFun a := ⟨a.1, Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) (a.1 + a.1) f a.2⟩
  map_mul' a b := Sigma.ext rfl (heq_of_eq (evenCup_pullback (R := ℂ) f a.1 b.1 a.2 b.2))

theorem IsAlgebraicEven.pullback (h_LineBundleCycles : CycleOperations.CM.Construction.LineBundleCyclesInput)
    {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (f : X.toOver ⟶ Y.toOver)
    {a : EvenAlgebra.CM.Construction.EvenClass (R := ℂ) (Betti.Scheme.schemePointSpace Y.toOver)} (ha : IsAlgebraicEven Y a) :
    IsAlgebraicEven X (evenPullback f a) :=
  ComplexOperations.CM.Construction.complex_pullback_algebraic h_LineBundleCycles f a.1 a.2 ha

def packH1Cup (X : TopCat.{0}) (p : ℕ)
    (v : Fin (p + p) → AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) X 1) : EvenAlgebra.CM.Construction.EvenClass (R := ℂ) X :=
  packEven X p (IteratedCup.CM.Construction.h1Cup ℂ X (p + p) v)

theorem packH1Cup_evenAppend (X : TopCat.{0}) (p q : ℕ)
    (u : Fin (p + p) → AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) X 1)
    (v : Fin (q + q) → AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) X 1) :
    packH1Cup X (p + q) (EvenAppend.CM.Construction.evenAppend p q u v) = packH1Cup X p u * packH1Cup X q v := by
  change packEven X (p + q) (IteratedCup.CM.Construction.h1Cup ℂ X ((p + q) + (p + q)) (EvenAppend.CM.Construction.evenAppend p q u v)) =
    packEven X (p + q) (ComplexOperations.CM.Construction.evenCup ℂ X p q (IteratedCup.CM.Construction.h1Cup ℂ X (p + p) u) (IteratedCup.CM.Construction.h1Cup ℂ X (q + q) v))
  exact congrArg (packEven X (p + q)) (EvenAppend.CM.Construction.h1Cup_evenAppend (R := ℂ) X p q u v)

def packPair (X : TopCat.{0}) (a b : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) X 1) :
    EvenAlgebra.CM.Construction.EvenClass (R := ℂ) X := packEven X 1 (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ) X 1 1 a b)

theorem packPair_cycle (X : TopCat.{0}) (a b c d : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) X 1) :
    packPair X a b * packPair X c d = packPair X a c * packPair X d b := by
  change packEven X 2 (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ) X 2 2
    (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ) X 1 1 a b) (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ) X 1 1 c d)) =
    packEven X 2 (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ) X 2 2
      (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ) X 1 1 a c) (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ) X 1 1 d b))
  exact congrArg (packEven X 2) (CupRegrouping.CM.SurfaceConstruction.cup1111_cycle (R := ℂ) X a b c d)

theorem switch_cup_regroup (X : TopCat.{0})
    (U L₁ L₂ : EvenAlgebra.CM.Construction.EvenClass (R := ℂ) X)
    (c₁ c₂ i₁ i₂ z₁ z₂ : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) X 1) :
    ((U * packPair X c₁ c₂) * (packPair X i₁ i₂ * packPair X z₁ z₂)) * (L₁ * L₂) =
      (U * packPair X z₁ z₂) *
        ((packPair X c₁ i₁ * L₁) * (packPair X i₂ c₂ * L₂)) := by
  rw [show ((U * packPair X c₁ c₂) * (packPair X i₁ i₂ * packPair X z₁ z₂)) * (L₁ * L₂) =
      (U * packPair X z₁ z₂) * ((packPair X c₁ c₂ * packPair X i₁ i₂) * (L₁ * L₂)) by ac_rfl]
  rw [packPair_cycle]
  ac_rfl

end AlgebraicGeometry.HodgeConjecture.CMReduction.PackedRegroup.CM.Construction

namespace AlgebraicGeometry.HodgeConjecture.CMReduction

/-! Extracting a class in a known degree, and naturality of packed
iterated cups. Each equality retains the actual cohomology coefficient map. -/

open _root_.CategoryTheory

def EvenAlgebra.CM.Construction.EvenClass.inDegree {X : TopCat.{0}} (a : EvenAlgebra.CM.Construction.EvenClass (R := ℂ) X) (p : ℕ) (hp : a.1 = p) :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) X (p + p) :=
  AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCast (TopCat.toSSet.obj X) (ModuleCat.of ℂ ℂ) (congrArg (fun n => n + n) hp) a.2

theorem PackedRegroup.CM.Construction.packEven_inDegree {X : TopCat.{0}} (a : EvenAlgebra.CM.Construction.EvenClass (R := ℂ) X) (p : ℕ) (hp : a.1 = p) :
    PackedRegroup.CM.Construction.packEven X p (a.inDegree p hp) = a := by
  apply Sigma.ext hp.symm
  exact EvenAlgebra.CM.Construction.cohomologyCast_heq (R := ℂ) X (congrArg (fun n => n + n) hp) a.2

theorem PackedRegroup.CM.Construction.evenPullback_pack {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) (p : ℕ)
    (a : Betti.Scheme.schemeBetti (ModuleCat.of ℂ ℂ) Y (p + p)) :
    PackedRegroup.CM.Construction.evenPullback f (PackedRegroup.CM.Construction.packEven (Betti.Scheme.schemePointSpace Y) p a) =
      PackedRegroup.CM.Construction.packEven (Betti.Scheme.schemePointSpace X) p (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) (p + p) f a) := rfl

theorem PackedRegroup.CM.Construction.evenPullback_comp {X Y Z : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) (g : Y ⟶ Z)
    (a : EvenAlgebra.CM.Construction.EvenClass (R := ℂ) (Betti.Scheme.schemePointSpace Z)) :
    PackedRegroup.CM.Construction.evenPullback f (PackedRegroup.CM.Construction.evenPullback g a) = PackedRegroup.CM.Construction.evenPullback (f ≫ g) a := by
  rcases a with ⟨p, a⟩
  exact congrArg (PackedRegroup.CM.Construction.packEven (Betti.Scheme.schemePointSpace X) p) (CupPullback.CM.Construction.scheme_pullback_comp (R := ℂ) f g (p + p) a)

theorem PackedRegroup.CM.Construction.evenPullback_H1Cup {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) (p : ℕ)
    (v : Fin (p + p) → Betti.Scheme.schemeBetti (ModuleCat.of ℂ ℂ) Y 1) :
    PackedRegroup.CM.Construction.evenPullback f (PackedRegroup.CM.Construction.packH1Cup (Betti.Scheme.schemePointSpace Y) p v) =
      PackedRegroup.CM.Construction.packH1Cup (Betti.Scheme.schemePointSpace X) p
        (fun i => Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 f (v i)) :=
  congrArg (PackedRegroup.CM.Construction.packEven (Betti.Scheme.schemePointSpace X) p) (CupAppend.CM.Construction.scheme_h1Cup_pullback (R := ℂ) f (p + p) v)

theorem PackedRegroup.CM.Construction.evenPullback_pair {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y)
    (a b : Betti.Scheme.schemeBetti (ModuleCat.of ℂ ℂ) Y 1) :
    PackedRegroup.CM.Construction.evenPullback f (PackedRegroup.CM.Construction.packPair (Betti.Scheme.schemePointSpace Y) a b) =
      PackedRegroup.CM.Construction.packPair (Betti.Scheme.schemePointSpace X)
        (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 f a) (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 f b) :=
  congrArg (PackedRegroup.CM.Construction.packEven (Betti.Scheme.schemePointSpace X) 1) (CupPullback.CM.Construction.scheme_cup_pullback (R := ℂ) f 1 1 a b)

theorem PackedRegroup.CM.Construction.packH1Cup_pair (X : TopCat.{0}) (a b : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) X 1) :
    PackedRegroup.CM.Construction.packH1Cup X 1 ![a, b] = PackedRegroup.CM.Construction.packPair X a b :=
  congrArg (PackedRegroup.CM.Construction.packEven X 1) (CupAppend.CM.Construction.h1Cup_two (R := ℂ) X ![a, b])

theorem PackedRegroup.CM.Construction.packH1Cup_four (X : TopCat.{0})
    (a b c d : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) X 1) :
    PackedRegroup.CM.Construction.packH1Cup X 2 ![a, b, c, d] = PackedRegroup.CM.Construction.packPair X a b * PackedRegroup.CM.Construction.packPair X c d :=
  congrArg (PackedRegroup.CM.Construction.packEven X 2) (CupAppend.CM.Construction.h1Cup_four (R := ℂ) X ![a, b, c, d])

end AlgebraicGeometry.HodgeConjecture.CMReduction

namespace AlgebraicGeometry.HodgeConjecture.CMReduction.PackedRegroup.CM.Construction

/-! Algebraicity of the exactly regrouped switch product. -/

open _root_.CategoryTheory

theorem pullback_switch_regroup
    {W X : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : W ⟶ X)
    (U : EvenAlgebra.CM.Construction.EvenClass (R := ℂ) (Betti.Scheme.schemePointSpace X))
    (L₁ L₂ : EvenAlgebra.CM.Construction.EvenClass (R := ℂ) (Betti.Scheme.schemePointSpace W))
    (c₁ c₂ i₁ i₂ : Betti.Scheme.schemeBetti (ModuleCat.of ℂ ℂ) W 1)
    (z₁ z₂ : Betti.Scheme.schemeBetti (ModuleCat.of ℂ ℂ) X 1) :
    ((evenPullback f U * packPair (Betti.Scheme.schemePointSpace W) c₁ c₂) *
      (packPair (Betti.Scheme.schemePointSpace W) i₁ i₂ * evenPullback f (packPair (Betti.Scheme.schemePointSpace X) z₁ z₂))) *
        (L₁ * L₂) =
    evenPullback f (U * packPair (Betti.Scheme.schemePointSpace X) z₁ z₂) *
      ((packPair (Betti.Scheme.schemePointSpace W) c₁ i₁ * L₁) * (packPair (Betti.Scheme.schemePointSpace W) i₂ c₂ * L₂)) := by
  rw [map_mul, evenPullback_pair]
  exact switch_cup_regroup (Betti.Scheme.schemePointSpace W) (evenPullback f U) L₁ L₂ c₁ c₂ i₁ i₂
    (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 f z₁) (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 f z₂)

theorem regroup_algebraic (h_LineBundleCycles : CycleOperations.CM.Construction.LineBundleCyclesInput) (h_ThomClass : CycleOperations.CM.Construction.ExteriorInput)
    {W X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (f : W.toOver ⟶ X.toOver)
    (U : EvenAlgebra.CM.Construction.EvenClass (R := ℂ) (Betti.Scheme.schemePointSpace X.toOver))
    (L₁ L₂ : EvenAlgebra.CM.Construction.EvenClass (R := ℂ) (Betti.Scheme.schemePointSpace W.toOver))
    (c₁ c₂ i₁ i₂ : W.complexCohomology 1) (z₁ z₂ : X.complexCohomology 1)
    (hprevious : IsAlgebraicEven W (evenPullback f U * packPair (Betti.Scheme.schemePointSpace W.toOver) c₁ c₂))
    (hswitch : IsAlgebraicEven W
      (packPair (Betti.Scheme.schemePointSpace W.toOver) i₁ i₂ * evenPullback f (packPair (Betti.Scheme.schemePointSpace X.toOver) z₁ z₂)))
    (hL₁ : IsAlgebraicEven W L₁) (hL₂ : IsAlgebraicEven W L₂) :
    IsAlgebraicEven W (evenPullback f (U * packPair (Betti.Scheme.schemePointSpace X.toOver) z₁ z₂) *
      ((packPair (Betti.Scheme.schemePointSpace W.toOver) c₁ i₁ * L₁) *
        (packPair (Betti.Scheme.schemePointSpace W.toOver) i₂ c₂ * L₂))) := by
  rw [← pullback_switch_regroup f U L₁ L₂ c₁ c₂ i₁ i₂ z₁ z₂]
  exact IsAlgebraicEven.mul h_LineBundleCycles h_ThomClass
    (IsAlgebraicEven.mul h_LineBundleCycles h_ThomClass hprevious hswitch)
    (IsAlgebraicEven.mul h_LineBundleCycles h_ThomClass hL₁ hL₂)

end AlgebraicGeometry.HodgeConjecture.CMReduction.PackedRegroup.CM.Construction

end

end OAI
